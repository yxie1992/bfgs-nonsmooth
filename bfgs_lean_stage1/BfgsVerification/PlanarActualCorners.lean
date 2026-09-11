import BfgsVerification.PlanarFieldRegularity

/-! Actual finite corner data selected from the source's local two-branch
hypothesis. The chart package is constructed, never assumed by the final
compact-level existence theorem. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarCornerCharts
open HomogeneousPlanar ConvexSubdifferential PlanarNormalGeometry

structure CornerChart (F : Vec 2 → ℝ) (x : Vec 2) where
  branches : Fin 2 → Vec 2 → ℝ
  curve : ℝ → Vec 2
  localMax : LocalFiniteMax F branches x
  branchesC2 : ∀ i, ContDiffAt ℝ 2 (branches i) x
  active : ∀ i, branches i x = F x
  curveAt : curve (F x) = x
  curveC2 : ContDiffAt ℝ 2 curve (F x)
  defining : ∀ᶠ t in 𝓝 (F x), ∀ i, branches i (curve t)=t
  commonRate : ∀ i, dot (coordinateGradient (branches i) x) (deriv curve (F x))=1

/-- The packaged data are obtained from the actual inverse-function theorem
for the two source branches. -/
theorem nonempty_cornerChart {F : Vec 2 → ℝ} {x : Vec 2}
    (hx : TwoBranchRegularAt F x) : Nonempty (CornerChart F x) := by
  obtain ⟨f,a,b,hrep,hC,h0,h1,hd,hf0,hf1⟩ := hx
  obtain ⟨p,hp,hpC,hlevel,_⟩ := exists_corner_chart hC h0 h1 hd hf0 hf1
  have hact : ∀ i, f i x=F x := by intro i; fin_cases i; exact hf0; exact hf1
  have hgrad : ∀ i, HasFDerivAt (f i) (gradientFunctional (coordinateGradient (f i) (p (F x)))) (p (F x)) := by
    intro i
    rw [hp]
    exact hasFDerivAt_coordinateGradient ((hC i).differentiableAt (by norm_num))
  have hrate := curve_velocity_pairing ((hpC.differentiableAt (by norm_num)).hasDerivAt) hgrad hlevel
  rw [hp] at hrate
  exact ⟨⟨f,p,hrep,hC,hact,hp,hpC,hlevel,hrate⟩⟩

theorem CornerChart.hasGradient {F : Vec 2 → ℝ} {x : Vec 2} (c : CornerChart F x) (i : Fin 2) :
    HasFDerivAt (c.branches i) (gradientFunctional (coordinateGradient (c.branches i) x)) x :=
  hasFDerivAt_coordinateGradient ((c.branchesC2 i).differentiableAt (by norm_num))

theorem CornerChart.supports {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {x : Vec 2} (c : CornerChart F x) (i : Fin 2) :
    Homogeneous.Supports F x (coordinateGradient (c.branches i) x) :=
  active_gradient_supports hF c.localMax c.hasGradient (mem_activeIndices.mpr (c.active i))

theorem CornerChart.velocityC1 {F : Vec 2 → ℝ} {x : Vec 2} (c : CornerChart F x) :
    ContDiffAt ℝ 1 (deriv c.curve) (F x) := curve_velocity_contDiffAt c.curveC2

/-- An independent active gradient pair cannot occur at a differentiable point
of the actual convex maximum. -/
theorem twoBranchRegular_not_differentiable {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {x : Vec 2} (hx : TwoBranchRegularAt F x) :
    ¬DifferentiableAt ℝ F x := by
  obtain ⟨f,a,b,hrep,hC,h0,h1,hd,hf0,hf1⟩ := hx
  intro hdiff
  let g : Fin 2 → Vec 2 := ![a,b]
  have hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have ha : Homogeneous.Supports F x a := active_gradient_supports hF hrep hg (mem_activeIndices.mpr hf0)
  have hb : Homogeneous.Supports F x b := active_gradient_supports hF hrep hg (mem_activeIndices.mpr hf1)
  have hgrad := hasFDerivAt_coordinateGradient hdiff
  have hab : a=b := (supporting_vector_eq_gradient ha hgrad).trans (supporting_vector_eq_gradient hb hgrad).symm
  apply hd
  rw [hab]
  simp only [pairDet]
  ring

/-- Every compact regular subset of one level admits a finite family of actual
corner charts. The empty corner family is included. -/
theorem exists_finite_cornerCharts {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec 2)} {ℓ : ℝ} (hK : IsCompact K) (hlevel : ∀ x ∈ K, F x=ℓ)
    (hregular : ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ TwoBranchRegularAt F x) :
    ∃ m : ℕ, ∃ points : Fin m → Vec 2, ∃ charts : ∀ i, CornerChart F (points i),
      Function.Injective points ∧ (∀ i, points i ∈ K ∧ ¬DifferentiableAt ℝ F (points i)) ∧
      ∀ x ∈ K, ContDiffAt ℝ 2 F x ∨ ∃ i, x=points i := by
  classical
  let S : Set (Vec 2) := {x ∈ K | ¬DifferentiableAt ℝ F x}
  have hS : S.Finite := finite_nonsmooth_on_compact_level hK hlevel hregular
  letI : Fintype S := hS.fintype
  let e := (Fintype.equivFin S).symm
  let points : Fin (Fintype.card S) → Vec 2 := fun i => (e i : Vec 2)
  have hpoint (i : Fin (Fintype.card S)) : points i ∈ K ∧ ¬DifferentiableAt ℝ F (points i) := (e i).property
  have hchart (i : Fin (Fintype.card S)) : Nonempty (CornerChart F (points i)) := by
    rcases hregular (points i) (hpoint i).1 with hs | hc
    · exact False.elim ((hpoint i).2 (hs.differentiableAt (by norm_num)))
    · exact nonempty_cornerChart hc
  refine ⟨Fintype.card S,points,fun i => Classical.choice (hchart i),?_,hpoint,?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro x hx
    rcases hregular x hx with hs | hc
    · exact Or.inl hs
    · right
      let z : S := ⟨x,hx,twoBranchRegular_not_differentiable hF hc⟩
      refine ⟨e.symm z,?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply z).symm

end PlanarCornerCharts
end BfgsVerification
