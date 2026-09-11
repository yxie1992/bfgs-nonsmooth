import BfgsVerification.PlanarFieldRegularity

/-! The actual derivative of C's comparison field preserves the level tangent
line. The proof uses intrinsic unit-normal identities and no angle chart. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarObjectiveField
open PlanarNormalGeometry PlanarAmbientFrame

theorem dot_smul_first (r : ℝ) (a b : Vec 2) : dot (r • a) b=r*dot a b :=
  Matrix.smul_dotProduct r a b

theorem dot_hasDerivAt {a b : ℝ → Vec 2} {a' b' : Vec 2} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => dot (a s) (b s)) (dot a' (b t)+dot (a t) b') t := by
  convert (((hasDerivAt_pi.mp ha) 0).mul ((hasDerivAt_pi.mp hb) 0)).add
    (((hasDerivAt_pi.mp ha) 1).mul ((hasDerivAt_pi.mp hb) 1)) using 1
  · simp only [dot,Fin.sum_univ_two]
  · simp only [dot,Fin.sum_univ_two]
    ring

theorem unit_curve_derivative_orthogonal {a : ℝ → Vec 2} {a' : Vec 2} {t : ℝ}
    (ha : HasDerivAt a a' t) (hu : ∀ᶠ s in 𝓝 t, sqNorm (a s)=1) : dot (a t) a'=0 := by
  have he : ∀ᶠ s in 𝓝 t, dot (a s) (a s)=1 := by
    filter_upwards [hu] with s hs
    exact (CertificateGeometry.dot_self _).trans hs
  have hzero := (dot_hasDerivAt ha ha).unique
    ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq he)
  have hc : dot a' (a t)=dot (a t) a' := dotProduct_comm _ _
  rw [hc] at hzero
  linarith

theorem tangent_vector_eq_rotate {w u : Vec 2} (hw : sqNorm w=1) (hu : dot w u=0) :
    u=dot (rotate w) u • rotate w := by
  have he := PlanarAmbientFrame.reconstruct hw u
  rw [hu,zero_smul,zero_add] at he
  exact he.symm

/-- A varying unit normal and a velocity family stationary to first order give
no normal component in the derivative of the actual joined frame. -/
theorem joined_frame_derivative_tangent {m : ℕ} {χ : Fin m → Vec 2 → ℝ}
    (hχ : ∀ i, Differentiable ℝ (χ i)) {v : Fin m → ℝ → Vec 2} {a : ℝ → Vec 2}
    {t : ℝ} {a' W' : Vec 2} (ha : HasDerivAt a a' t)
    (hv : ∀ i, HasDerivAt (v i) (0 : Vec 2) t)
    (hu : ∀ᶠ s in 𝓝 t, sqNorm (a s)=1)
    (hframe : HasDerivAt (fun s => PlanarAmbientFrame.frame χ (fun i => v i s) (a s)) W' t) :
    dot (a t) W'=0 := by
  let β : ℝ := dot (rotate (a t)) a'
  have hunit : sqNorm (a t)=1 := hu.self_of_nhds
  have hap : a'=β • rotate (a t) := tangent_vector_eq_rotate hunit (unit_curve_derivative_orthogonal ha hu)
  have hheight : HasDerivAt (fun s => PlanarAmbientFrame.height χ (fun i => v i s) (a s))
      (β*angularSlope χ (fun i => v i t) (a t)) t := by
    have hi (i : Fin m) := ((hχ i (a t)).hasFDerivAt.comp_hasDerivAt t ha).mul
      ((dot_hasDerivAt ha (hv i)).sub_const 1)
    have hs := (HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i)).const_add 1
    have hz : dot (a t) (0 : Vec 2)=0 := by simp [dot]
    convert hs using 1
    simp only [angularSlope,Finset.mul_sum,hap,ContinuousLinearMap.map_smul,
      dot_smul_first,smul_eq_mul,Function.comp_apply,hz,add_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdot := dot_hasDerivAt ha hframe
  have he : ∀ᶠ s in 𝓝 t,
      dot (a s) (PlanarAmbientFrame.frame χ (fun i => v i s) (a s))=
        PlanarAmbientFrame.height χ (fun i => v i s) (a s) := by
    filter_upwards [hu] with s hs
    exact PlanarAmbientFrame.normal_pairing χ _ hs
  have hderiv := hdot.unique (hheight.congr_of_eventuallyEq he)
  have hrot : dot (rotate (a t)) (rotate (a t))=1 := by
    simp only [sqNorm,Fin.sum_univ_two] at hunit
    simpa [dot,rotate,Fin.sum_univ_two,add_comm,pow_two] using hunit
  have horth : dot (rotate (a t)) (a t)=0 := by
    rw [show dot (rotate (a t)) (a t)=dot (a t) (rotate (a t)) from dotProduct_comm _ _]
    exact rotate_orthogonal _
  have hpair : dot a' (PlanarAmbientFrame.frame χ (fun i => v i t) (a t))=
      β*angularSlope χ (fun i => v i t) (a t) := by
    rw [hap,dot_smul_first,PlanarAmbientFrame.frame]
    change β*dotProduct (rotate (a t)) (_ • a t+_ • rotate (a t))=_
    rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
    change β*(_*dot (rotate (a t)) (a t)+_*dot (rotate (a t)) (rotate (a t)))=_
    rw [hrot,horth]
    ring
  rw [hpair] at hderiv
  linarith

/-- Source C.194: the actual Fréchet derivative of the actual objective field
preserves the one-dimensional tangent line of every smooth nonstationary level. -/
theorem actual_field_derivative_preserves_tangent {m : ℕ} {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {χ : Fin m → Vec 2 → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    {v : Fin m → ℝ → Vec 2} {x s : Vec 2}
    (hv : ∀ i, ContDiffAt ℝ 1 (v i) (F x)) (hFx : ContDiffAt ℝ 2 F x)
    (hne : coordinateGradient F x ≠ 0) (hs : dot (coordinateGradient F x) s=0) :
    dot (coordinateGradient F x) ((fderiv ℝ (field hF χ v) x) s)=0 := by
  let line (t : ℝ) := x+t • s
  have hl : HasDerivAt line s 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add x
  have hl0 : line 0=x := by simp [line]
  have hgC : ContDiffAt ℝ 1 (coordinateGradient F) x := by
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hFx.fderiv_right (by norm_num)
    apply contDiffAt_pi.mpr
    intro i
    exact hfd.clm_apply contDiffAt_const
  have hnC : ContDiffAt ℝ 1 (fun z => normalized (coordinateGradient F z)) x :=
    ((normalized_contDiffAt hne).of_le (by norm_num)).comp x hgC
  let normalCurve (t : ℝ) := normalized (coordinateGradient F (line t))
  have hnormal : DifferentiableAt ℝ normalCurve 0 :=
    ((hnC.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl hl0.symm).differentiableAt
  have hvalue : HasDerivAt (fun t => F (line t)) (0 : ℝ) 0 := by
    have hd := (hasFDerivAt_coordinateGradient (hFx.differentiableAt (by norm_num))).comp_hasDerivAt_of_eq 0 hl hl0.symm
    simpa only [gradientFunctional_apply,hs] using hd
  have hvel (i : Fin m) : HasDerivAt (fun t => v i (F (line t))) (0 : Vec 2) 0 := by
    have hd := ((hv i).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hvalue (by rw [hl0])
    simpa only [map_zero] using hd
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ), sqNorm (normalCurve t)=1 := by
    have hng : ∀ᶠ z in 𝓝 x, coordinateGradient F z ≠ 0 := hgC.continuousAt.eventually_ne hne
    filter_upwards [(hl.continuousAt.tendsto.mono_right (by rw [hl0])).eventually hng] with t ht
    exact normalized_sqNorm ht
  have hW := (field_contDiffAt_smooth hF hχ hv hFx hne).differentiableAt (by norm_num)
  have hWline := hW.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl hl0.symm
  have hframe : HasDerivAt (fun t => PlanarAmbientFrame.frame χ (fun i => v i (F (line t))) (normalCurve t))
      ((fderiv ℝ (field hF χ v) x) s) 0 := by
    apply hWline.congr_of_eventuallyEq
    filter_upwards [(hl.continuousAt.tendsto.mono_right (by rw [hl0])).eventually (hFx.eventually (by norm_num))] with t ht
    exact (field_eq_gradient_formula hF χ v (hasFDerivAt_coordinateGradient (ht.differentiableAt (by norm_num)))).symm
  have hout := joined_frame_derivative_tangent (fun i => (hχ i).differentiable (by norm_num))
    hnormal.hasDerivAt hvel hunit hframe
  change dot (normalized (coordinateGradient F (line 0))) _=0 at hout
  rw [hl0,normalized,dot_smul_first] at hout
  exact (mul_eq_zero.mp hout).resolve_left (inv_ne_zero (by
    intro he
    exact hne (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) (norm_eq_zero.mp he))))

end PlanarObjectiveField
end BfgsVerification
