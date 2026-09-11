import BfgsVerification.FixedNormalVisibility

/-! Local C1,1 regularity for the actual scalar composite off its interface. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix
namespace BfgsVerification.FixedNormal
open CenteredSmoothSublinear

/-- Standard local C1,1 for a scalar function, stated with its actual derivative. -/
def ScalarLocallyC11On (U : Set ℝ) (h : ℝ → ℝ) : Prop :=
  DifferentiableOn ℝ h U ∧ LocallyLipschitzOn U (fderiv ℝ h)

theorem normalCoordinate_hasFDerivAt {n : ℕ} (a : Vec n) (b : ℝ) (x : Vec n) :
    HasFDerivAt (normalCoordinate a b) (gradientFunctional a) x := by
  simpa only [normalCoordinate, gradientFunctional_apply] using
    (gradientFunctional a).hasFDerivAt.sub_const b

theorem normalCoordinate_lipschitz {n : ℕ} (a : Vec n) (b : ℝ) :
    LipschitzWith ‖gradientFunctional a‖₊ (normalCoordinate a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  have he : normalCoordinate a b x - normalCoordinate a b z = gradientFunctional a (x - z) := by
    simp only [normalCoordinate, gradientFunctional_apply]
    change a ⬝ᵥ x - b - (a ⬝ᵥ z - b) = a ⬝ᵥ (x - z)
    rw [dotProduct_sub]
    ring
  simp only [dist_eq_norm, he, NNReal.coe_mk]
  exact (gradientFunctional a).le_opNorm _

/-- The composite's full gradient is locally Lipschitz off the exceptional
normal level, derived from local regularity of both original summands. -/
theorem composite_locallyC11_off_interface {n : ℕ} {F ψ : Vec n → ℝ} {h : ℝ → ℝ}
    {Ω : Set (Vec n)} (hΩ : IsOpen Ω) (hψ : LocallyC11On Ω ψ)
    (a : Vec n) (b : ℝ) {E : Set ℝ} (hE : IsClosed E)
    (hh : ScalarLocallyC11On Eᶜ h)
    (hrep : ∀ x ∈ Ω, F x = ψ x + h (normalCoordinate a b x)) :
    LocallyC11On (regularRegion Ω a b E) F := by
  let S := regularRegion Ω a b E
  let l := gradientFunctional a
  have hS : IsOpen S := isOpen_regularRegion hΩ a b hE
  have hd (x : Vec n) (hx : x ∈ S) : HasFDerivAt F
      (fderiv ℝ ψ x + (fderiv ℝ h (normalCoordinate a b x)).comp l) x := by
    have hp := ((hψ.1 x hx.1).differentiableAt (hΩ.mem_nhds hx.1)).hasFDerivAt
    have hh' := ((hh.1 (normalCoordinate a b x) hx.2).differentiableAt (hE.isOpen_compl.mem_nhds hx.2)).hasFDerivAt
    have hc := hp.add (hh'.comp x (normalCoordinate_hasFDerivAt a b x))
    apply hc.congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hx.1] with z hz
    exact hrep z hz
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_⟩
  intro x hx
  obtain ⟨M, V, hV, hMV⟩ := hψ.2 hx.1
  obtain ⟨N, W, hW, hNW⟩ := hh.2 hx.2
  have hV' : V ∈ 𝓝 x := by rwa [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hx.1)] at hV
  have hW' : W ∈ 𝓝 (normalCoordinate a b x) := by
    rwa [nhdsWithin_eq_nhds.mpr (hE.isOpen_compl.mem_nhds hx.2)] at hW
  let Q := V ∩ (normalCoordinate a b) ⁻¹' W ∩ S
  have hQ : Q ∈ 𝓝 x := inter_mem
    (inter_mem hV' ((continuous_normalCoordinate a b).tendsto x hW')) (hS.mem_nhds hx)
  let C : ℝ≥0 := M + N * ‖l‖₊ ^ 2
  refine ⟨C, Q, mem_nhdsWithin_of_mem_nhds hQ, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  simp only [dist_eq_norm]
  rw [(hd y hy.2).fderiv, (hd z hz.2).fderiv]
  have hdiff : (fderiv ℝ ψ y + (fderiv ℝ h (normalCoordinate a b y)).comp l) -
      (fderiv ℝ ψ z + (fderiv ℝ h (normalCoordinate a b z)).comp l) =
      (fderiv ℝ ψ y - fderiv ℝ ψ z) +
        (fderiv ℝ h (normalCoordinate a b y) - fderiv ℝ h (normalCoordinate a b z)).comp l := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    ring
  rw [hdiff]
  have hp := hMV.norm_sub_le hy.1.1 hz.1.1
  have hh' := hNW.norm_sub_le hy.1.2 hz.1.2
  have hr := (normalCoordinate_lipschitz a b).norm_sub_le y z
  calc
    _ ≤ ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ +
        ‖(fderiv ℝ h (normalCoordinate a b y) - fderiv ℝ h (normalCoordinate a b z)).comp l‖ := norm_add_le _ _
    _ ≤ (M : ℝ) * ‖y - z‖ +
        ‖fderiv ℝ h (normalCoordinate a b y) - fderiv ℝ h (normalCoordinate a b z)‖ * ‖l‖ :=
      add_le_add hp ((fderiv ℝ h (normalCoordinate a b y) - fderiv ℝ h (normalCoordinate a b z)).opNorm_comp_le l)
    _ ≤ (M : ℝ) * ‖y - z‖ +
        ((N : ℝ) * (‖l‖ * ‖y - z‖)) * ‖l‖ := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact hh'.trans (mul_le_mul_of_nonneg_left (by simpa [l] using hr) N.coe_nonneg)
    _ = (C : ℝ) * ‖y - z‖ := by simp only [C, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm]; ring

end BfgsVerification.FixedNormal
