import BfgsVerification.PlanarJoinedFrame

/-! A branch-free formula for C's angular frame on the plane. Differentiating
ambient cutoff functions in the rotated normal direction implements the actual
angular derivative without choosing an angle chart. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix Function
namespace BfgsVerification
namespace PlanarAmbientFrame
open PlanarTransport

def rotate (w : Vec 2) : Vec 2 := ![-w 1,w 0]

def height {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) (w : Vec 2) : ℝ :=
  1+∑ i, χ i w*(dot w (v i)-1)

def angularSlope {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) (w : Vec 2) : ℝ :=
  ∑ i, ((fderiv ℝ (χ i) w) (rotate w)*(dot w (v i)-1)+χ i w*dot (rotate w) (v i))

def frame {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) (w : Vec 2) : Vec 2 :=
  height χ v w • w+angularSlope χ v w • rotate w

theorem rotate_normal (θ : ℝ) : rotate (normal θ)=tangent θ := by
  ext i
  fin_cases i <;> simp [rotate,normal,tangent]

theorem rotate_orthogonal (w : Vec 2) : dot w (rotate w)=0 := by
  simp [dot,rotate,Fin.sum_univ_two]
  ring

theorem reconstruct {w : Vec 2} (hw : sqNorm w=1) (v : Vec 2) :
    dot w v • w+dot (rotate w) v • rotate w=v := by
  simp only [sqNorm,Fin.sum_univ_two] at hw
  ext i
  fin_cases i <;> simp [dot,rotate,Fin.sum_univ_two]
  · nlinarith [congrArg (fun s : ℝ => s*v 0) hw]
  · nlinarith [congrArg (fun s : ℝ => s*v 1) hw]

/-- The ambient slope formula is exactly the actual angular derivative. -/
theorem angularSlope_eq_deriv {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hχ : ∀ i, Differentiable ℝ (χ i)) (θ : ℝ) :
    angularSlope χ v (normal θ)=deriv (PlanarJoinedFrame.height χ v) θ := by
  have hn := normal_hasDerivAt θ
  have hi (i : Fin m) : HasDerivAt
      (fun φ => χ i (normal φ)*(dot (normal φ) (v i)-1))
      ((fderiv ℝ (χ i) (normal θ)) (rotate (normal θ))*(dot (normal θ) (v i)-1)+
        χ i (normal θ)*dot (rotate (normal θ)) (v i)) θ := by
    have hc := (hχ i (normal θ)).hasFDerivAt.comp_hasDerivAt θ hn
    have hv := (gradientFunctional (v i)).hasFDerivAt.comp_hasDerivAt θ hn
    have hd : HasDerivAt (fun φ => dot (normal φ) (v i)) (dot (tangent θ) (v i)) θ := by
      simpa only [gradientFunctional_apply,dot,mul_comm] using hv
    simpa only [rotate_normal] using hc.mul (hd.sub_const 1)
  have hs := (HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i)).const_add 1
  exact hs.deriv.symm

theorem frame_eq_angular_frame {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hχ : ∀ i, Differentiable ℝ (χ i)) (θ : ℝ) :
    frame χ v (normal θ)=PlanarJoinedFrame.frame χ v θ := by
  rw [frame,angularSlope_eq_deriv v hχ θ,rotate_normal]
  rfl

theorem cutoff_derivatives_zero_on_plateau {m : ℕ} {χ : Fin m → Vec 2 → ℝ}
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} {w : Vec 2} (hi : ∀ᶠ z in 𝓝 w, χ i z=1) :
    ∀ j, fderiv ℝ (χ j) w=0 := by
  intro j
  by_cases hji : j=i
  · subst j
    exact ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) w).congr_of_eventuallyEq hi).fderiv
  · have hj : ∀ᶠ z in 𝓝 w, χ j z=0 := by
      filter_upwards [hi] with z hz
      exact PlanarJoinedFrame.cutoff_other_zero hd (by rw [hz]; norm_num) hji
    exact ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) w).congr_of_eventuallyEq hj).fderiv

/-- Plateau recovery holds for every Euclidean unit normal directly, with no
angle existence or angular branch-cut assumption. -/
theorem frame_eq_velocity {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} {w : Vec 2} (hw : sqNorm w=1) (hi : ∀ᶠ z in 𝓝 w, χ i z=1) :
    frame χ v w=v i := by
  have hiz : χ i w=1 := hi.self_of_nhds
  have hother (j : Fin m) (hji : j ≠ i) : χ j w=0 :=
    PlanarJoinedFrame.cutoff_other_zero hd (by rw [hiz]; norm_num) hji
  have hh : height χ v w=dot w (v i) := by
    rw [height,Finset.sum_eq_single i]
    · rw [hiz]
      ring
    · intro j _ hji
      rw [hother j hji,zero_mul]
    · simp
  have hs : angularSlope χ v w=dot (rotate w) (v i) := by
    simp only [angularSlope,cutoff_derivatives_zero_on_plateau hd hi,
      ContinuousLinearMap.zero_apply,zero_mul,zero_add]
    rw [Finset.sum_eq_single i]
    · rw [hiz,one_mul]
    · intro j _ hji
      rw [hother j hji,zero_mul]
    · simp
  rw [frame,hh,hs]
  exact reconstruct hw (v i)

theorem normal_pairing {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2)
    {w : Vec 2} (hw : sqNorm w=1) : dot w (frame χ v w)=height χ v w := by
  have hn : dot w w=1 := (CertificateGeometry.dot_self w).trans hw
  change dotProduct w (height χ v w • w+angularSlope χ v w • rotate w)=_
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
  change height χ v w*dot w w+angularSlope χ v w*dot w (rotate w)=_
  rw [hn,rotate_orthogonal]
  ring

/-- The joined height is positive directly for ambient normals, without an
angular representation. -/
theorem height_pos {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hχ : ∀ i w, χ i w ∈ Icc (0 : ℝ) 1)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {w : Vec 2} (hpos : ∀ i, χ i w ≠ 0 → 0 < dot w (v i)) : 0 < height χ v w := by
  by_cases he : ∃ i, χ i w ≠ 0
  · obtain ⟨i,hi⟩ := he
    have heq : height χ v w=1+χ i w*(dot w (v i)-1) := by
      unfold height
      congr 1
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [PlanarJoinedFrame.cutoff_other_zero hd hi hji,zero_mul]
      · simp
    rw [heq]
    have hc := hχ i w
    have hcpos : 0 < χ i w := lt_of_le_of_ne hc.1 (fun h => hi h.symm)
    have hp := mul_pos hcpos (hpos i hi)
    nlinarith [hc.2]
  · push_neg at he
    simp only [height,he,zero_mul,Finset.sum_const_zero,add_zero]
    norm_num

end PlanarAmbientFrame
end BfgsVerification
