import BfgsVerification.PlanarSupportNeighborhoods
import BfgsVerification.PlanarAmbientFrame

/-! The joined comparison field of the actual objective. A support is selected
only to define the function globally; local formulas remove any dependence on
that arbitrary selection in every smooth or corner chart used in C. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Function
namespace BfgsVerification
namespace PlanarObjectiveField
open ConvexSubdifferential PlanarNormalGeometry

def selectedSupport {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (x : Vec n) : Vec n :=
  Classical.choose (subdifferential_nonempty hF x)

theorem selectedSupport_mem {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (x : Vec n) :
    selectedSupport hF x ∈ subdifferential F x := Classical.choose_spec (subdifferential_nonempty hF x)

theorem selectedSupport_eq_gradient {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {x g : Vec n} (hg : HasFDerivAt F (gradientFunctional g) x) : selectedSupport hF x=g :=
  supporting_vector_eq_gradient (selectedSupport_mem hF x) hg

theorem normalized_sqNorm {n : ℕ} {g : Vec n} (hg : g ≠ 0) : sqNorm (normalized g)=1 := by
  have hn : euclideanVector g ≠ 0 := by
    intro he
    exact hg (congrArg (fun v : EuclideanSpace ℝ (Fin n) => fun i => v i) he)
  have hn' := norm_ne_zero_iff.mpr hn
  have he : sqNorm g=‖euclideanVector g‖^2 := (FrameNorms.euclidean_norm_sq (euclideanVector g)).symm
  rw [normalized,CertificateGeometry.sqNorm_smul,he]
  field_simp

def field {m : ℕ} {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2) (x : Vec 2) : Vec 2 :=
  PlanarAmbientFrame.frame χ (fun i => v i (F x)) (normalized (selectedSupport hF x))

/-- At differentiable points the selected support is necessarily the actual
gradient, so the field has the literal source normal-gradient formula. -/
theorem field_eq_gradient_formula {m : ℕ} {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2)
    {x g : Vec 2} (hg : HasFDerivAt F (gradientFunctional g) x) :
    field hF χ v x=PlanarAmbientFrame.frame χ (fun i => v i (F x)) (normalized g) := by
  rw [field,selectedSupport_eq_gradient hF hg]

/-- At a corner, upper neighborhood control of all actual supports puts both
sides and the switching set on the same fixed cutoff plateau. Thus the actual
objective field equals the corresponding level velocity on a neighborhood. -/
theorem field_eventually_eq_corner_velocity {m : ℕ} {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin 2 → Vec 2 → ℝ} {g : Fin 2 → Vec 2} {x u : Vec 2}
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ j, HasFDerivAt (f j) (gradientFunctional (g j)) x)
    (hact : ∀ j, f j x=F x) (hu : ∀ j, dot (g j) u=1)
    {χ : Fin m → Vec 2 → ℝ} (v : Fin m → ℝ → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} (hχ : ∀ᶠ w in 𝓝ˢ (normalSector (g 0) (g 1)), χ i w=1) :
    ∀ᶠ z in 𝓝 x, field hF χ v z=v i (F z) := by
  filter_upwards [all_supports_in_corner_plateau hF hrep hg hact hu hχ] with z hz
  have hsel := hz _ (selectedSupport_mem hF z)
  exact PlanarAmbientFrame.frame_eq_velocity (fun j => v j (F z)) hd
    (normalized_sqNorm hsel.1) hsel.2

/-- The C1 level velocity composed with a finite convex objective is locally
Lipschitz. This includes arbitrarily many switches along line segments. -/
theorem lipschitz_near_of_eq_level_velocity {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {W : Vec 2 → Vec 2} {v : ℝ → Vec 2} {x : Vec 2}
    (hv : ContDiffAt ℝ 1 v (F x)) (hW : ∀ᶠ z in 𝓝 x, W z=v (F z)) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L W U := by
  obtain ⟨LF,U,hU,hLF⟩ := hF.locallyLipschitz x
  obtain ⟨Lv,V,hV,hLv⟩ := hv.exists_lipschitzOnWith
  let S : Set (Vec 2) := U ∩ F ⁻¹' V ∩ {z | W z=v (F z)}
  have hS : S ∈ 𝓝 x := inter_mem (inter_mem hU ((convex_continuous hF).tendsto x hV)) hW
  have hcomp : LipschitzOnWith (Lv*LF) (v ∘ F) S :=
    hLv.comp (hLF.mono (fun z hz => hz.1.1)) (fun z hz => hz.1.2)
  refine ⟨Lv*LF,S,hS,?_⟩
  intro z hz w hw
  rw [hz.2,hw.2]
  exact hcomp hz hw

/-- No regularity of the selected support enters corner continuity. -/
theorem field_continuousAt_corner {m : ℕ} {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {χ : Fin m → Vec 2 → ℝ} {v : Fin m → ℝ → Vec 2} {x : Vec 2} {i : Fin m}
    (hv : ContinuousAt (v i) (F x))
    (hfield : ∀ᶠ z in 𝓝 x, field hF χ v z=v i (F z)) : ContinuousAt (field hF χ v) x :=
  (hv.comp (convex_continuous hF).continuousAt).congr_of_eventuallyEq hfield

/-- At an actual regular corner the field pairs to one with every actual
subgradient, provided the velocity family uses its actual common level rate. -/
theorem field_supports_pairing_corner {m : ℕ} {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin 2 → Vec 2 → ℝ} {g : Fin 2 → Vec 2} {x u : Vec 2}
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ j, HasFDerivAt (f j) (gradientFunctional (g j)) x)
    (hact : ∀ j, f j x=F x) (hu : ∀ j, dot (g j) u=1)
    {χ : Fin m → Vec 2 → ℝ} (v : Fin m → ℝ → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} (hχ : ∀ᶠ w in 𝓝ˢ (normalSector (g 0) (g 1)), χ i w=1)
    (hv : v i (F x)=u) : ∀ a ∈ subdifferential F x, dot a (field hF χ v x)=1 := by
  have he := (field_eventually_eq_corner_velocity hF hrep hg hact hu v hd hχ).self_of_nhds
  rw [he,hv]
  exact two_branch_support_pairing hF hrep hg hact hu

/-- At a differentiable point this is the literal source visibility identity
with the actual Euclidean gradient length. -/
theorem field_gradient_pairing {m : ℕ} {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2)
    {x g : Vec 2} (hg : HasFDerivAt F (gradientFunctional g) x) (hne : g ≠ 0) :
    dot g (field hF χ v x)=‖euclideanVector g‖*
      PlanarAmbientFrame.height χ (fun i => v i (F x)) (normalized g) := by
  have heuc : euclideanVector g ≠ 0 := by
    intro he
    exact hne (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) he)
  have hn := norm_ne_zero_iff.mpr heuc
  have he : g=‖euclideanVector g‖ • normalized g := by
    rw [normalized,smul_smul,mul_inv_cancel₀ hn,one_smul]
  rw [field_eq_gradient_formula hF χ v hg]
  conv_lhs => arg 1; rw [he]
  change dotProduct (‖euclideanVector g‖ • normalized g) _=_
  rw [smul_dotProduct]
  change ‖euclideanVector g‖*dot (normalized g) _=_
  rw [PlanarAmbientFrame.normal_pairing χ _ (normalized_sqNorm hne)]

end PlanarObjectiveField
end BfgsVerification
