import BfgsVerification.PlanarObjectiveField

/-! Actual C1 regularity in smooth charts and local Lipschitz regularity in
corner charts for C's comparison field. -/
noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Function
namespace BfgsVerification
namespace PlanarObjectiveField
open ConvexSubdifferential PlanarNormalGeometry

theorem normalized_contDiffAt {n : ℕ} {g : Vec n} (hg : g ≠ 0) :
    ContDiffAt ℝ ∞ (normalized : Vec n → Vec n) g := by
  have hn : euclideanVector g ≠ 0 := by
    intro he
    exact hg (congrArg (fun v : EuclideanSpace ℝ (Fin n) => fun i => v i) he)
  have hc : ContDiff ℝ ∞ (euclideanVector : Vec n → EuclideanSpace ℝ (Fin n)) :=
    (WithLp.linearEquiv 2 ℝ (Vec n)).symm.toContinuousLinearEquiv.contDiff
  have hnorm := (contDiffAt_norm ℝ hn).comp g hc.contDiffAt
  exact (hnorm.inv (norm_ne_zero_iff.mpr hn)).smul contDiffAt_id

theorem dot_contDiffAt {u v : Vec 2 → Vec 2} {x : Vec 2}
    (hu : ContDiffAt ℝ 1 u x) (hv : ContDiffAt ℝ 1 v x) :
    ContDiffAt ℝ 1 (fun z => dot (u z) (v z)) x := by
  simp only [dot,Fin.sum_univ_two]
  exact (((contDiffAt_pi.mp hu) 0).mul ((contDiffAt_pi.mp hv) 0)).add
    (((contDiffAt_pi.mp hu) 1).mul ((contDiffAt_pi.mp hv) 1))

theorem ambient_frame_contDiffAt {m : ℕ} {χ : Fin m → Vec 2 → ℝ}
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) {v : Fin m → Vec 2 → Vec 2} {w : Vec 2 → Vec 2} {x : Vec 2}
    (hv : ∀ i, ContDiffAt ℝ 1 (v i) x) (hw : ContDiffAt ℝ 1 w x) :
    ContDiffAt ℝ 1 (fun z => PlanarAmbientFrame.frame χ (fun i => v i z) (w z)) x := by
  have hr : ContDiffAt ℝ 1 (fun z => PlanarAmbientFrame.rotate (w z)) x := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact ((contDiffAt_pi.mp hw) 1).neg
    · exact (contDiffAt_pi.mp hw) 0
  have hcc (i : Fin m) : ContDiffAt ℝ 1 (fun z => χ i (w z)) x :=
    ((hχ i).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contDiffAt.comp x hw
  have hd (i : Fin m) : ContDiffAt ℝ 1 (fun z => (fderiv ℝ (χ i) (w z)) (PlanarAmbientFrame.rotate (w z))) x := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ (χ i)) := ((hχ i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).fderiv_right (by norm_num)
    exact (hfd.contDiffAt.comp x hw).clm_apply hr
  have hheight : ContDiffAt ℝ 1 (fun z => PlanarAmbientFrame.height χ (fun i => v i z) (w z)) x := by
    apply contDiffAt_const.add
    apply ContDiffAt.sum
    intro i _
    exact (hcc i).mul ((dot_contDiffAt hw (hv i)).sub contDiffAt_const)
  have hslope : ContDiffAt ℝ 1 (fun z => PlanarAmbientFrame.angularSlope χ (fun i => v i z) (w z)) x := by
    apply ContDiffAt.sum
    intro i _
    exact ((hd i).mul ((dot_contDiffAt hw (hv i)).sub contDiffAt_const)).add
      ((hcc i).mul (dot_contDiffAt hr (hv i)))
  exact (hheight.smul hw).add (hslope.smul hr)

/-- On a genuinely smooth nonstationary chart, the actual objective field is
C1 even though its global definition used an arbitrary actual support. -/
theorem field_contDiffAt_smooth {m : ℕ} {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {χ : Fin m → Vec 2 → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    {v : Fin m → ℝ → Vec 2} {x : Vec 2} (hv : ∀ i, ContDiffAt ℝ 1 (v i) (F x))
    (hFx : ContDiffAt ℝ 2 F x) (hne : coordinateGradient F x ≠ 0) :
    ContDiffAt ℝ 1 (field hF χ v) x := by
  have hgC : ContDiffAt ℝ 1 (coordinateGradient F) x := by
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hFx.fderiv_right (by norm_num)
    apply contDiffAt_pi.mpr
    intro i
    exact hfd.clm_apply contDiffAt_const
  have hnC : ContDiffAt ℝ 1 (fun z => normalized (coordinateGradient F z)) x :=
    ((normalized_contDiffAt hne).of_le (by norm_num)).comp x hgC
  have hvc (i : Fin m) : ContDiffAt ℝ 1 (fun z => v i (F z)) x :=
    (hv i).comp x (hFx.of_le (by norm_num))
  apply (ambient_frame_contDiffAt hχ hvc hnC).congr_of_eventuallyEq
  filter_upwards [hFx.eventually (by norm_num)] with z hz
  exact field_eq_gradient_formula hF χ v
    (hasFDerivAt_coordinateGradient (hz.differentiableAt (by norm_num)))

/-- The complete corner Lipschitz statement discharges the local field identity
from the actual local maximum and the constructed sector plateau. -/
theorem field_lipschitz_near_corner {m : ℕ} {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin 2 → Vec 2 → ℝ} {g : Fin 2 → Vec 2} {x u : Vec 2}
    (hrep : LocalFiniteMax F f x)
    (hg : ∀ j, HasFDerivAt (f j) (gradientFunctional (g j)) x)
    (hact : ∀ j, f j x=F x) (hu : ∀ j, dot (g j) u=1)
    {χ : Fin m → Vec 2 → ℝ} (v : Fin m → ℝ → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} (hχ : ∀ᶠ w in 𝓝ˢ (normalSector (g 0) (g 1)), χ i w=1)
    (hv : ContDiffAt ℝ 1 (v i) (F x)) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith L (field hF χ v) U :=
  lipschitz_near_of_eq_level_velocity hF hv
    (field_eventually_eq_corner_velocity hF hrep hg hact hu v hd hχ)

end PlanarObjectiveField
end BfgsVerification
