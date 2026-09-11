import BfgsVerification.PlanarSectorCutoffs

/-! The source's finite joining formula has actual positive height and exactly
recovers each common-level velocity on its cutoff plateau. Angular derivatives
are actual derivatives, not independently supplied coefficients. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix Function
namespace BfgsVerification
namespace PlanarJoinedFrame
open PlanarTransport

def height {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) (θ : ℝ) : ℝ :=
  1+∑ i, χ i (normal θ)*(dot (normal θ) (v i)-1)

def frame {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) (θ : ℝ) : Vec 2 :=
  angularFrame (height χ v) (deriv (height χ v)) θ

theorem cutoff_other_zero {m : ℕ} {χ : Fin m → Vec 2 → ℝ}
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i j : Fin m} {w : Vec 2} (hi : χ i w ≠ 0) (hji : j ≠ i) : χ j w=0 := by
  by_contra hj
  exact Set.disjoint_left.mp (hd hji) hj hi

theorem height_eq_single {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} {θ : ℝ} (hi : χ i (normal θ) ≠ 0) :
    height χ v θ=1+χ i (normal θ)*(dot (normal θ) (v i)-1) := by
  unfold height
  congr 1
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [cutoff_other_zero hd hi hji,zero_mul]
  · simp

/-- At every angle the height is a convex combination of one and at most one
positive common-velocity pairing. The empty family is included. -/
theorem height_pos {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hχ : ∀ i w, χ i w ∈ Icc (0 : ℝ) 1)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {θ : ℝ} (hpos : ∀ i, χ i (normal θ) ≠ 0 → 0 < dot (normal θ) (v i)) :
    0 < height χ v θ := by
  by_cases he : ∃ i, χ i (normal θ) ≠ 0
  · obtain ⟨i,hi⟩ := he
    rw [height_eq_single v hd hi]
    have hc := hχ i (normal θ)
    have hcpos : 0 < χ i (normal θ) := lt_of_le_of_ne hc.1 (fun h => hi h.symm)
    have hp := mul_pos hcpos (hpos i hi)
    nlinarith [hc.2]
  · push_neg at he
    simp only [height,he,zero_mul,Finset.sum_const_zero,add_zero]
    norm_num

theorem height_lower_bound {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hχ : ∀ i w, χ i w ∈ Icc (0 : ℝ) 1)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {η θ : ℝ} (hη : η ≤ 1)
    (hbound : ∀ i, χ i (normal θ) ≠ 0 → η ≤ dot (normal θ) (v i)) :
    η ≤ height χ v θ := by
  by_cases he : ∃ i, χ i (normal θ) ≠ 0
  · obtain ⟨i,hi⟩ := he
    rw [height_eq_single v hd hi]
    have hc := hχ i (normal θ)
    have hp := mul_le_mul_of_nonneg_left (hbound i hi) hc.1
    have hq := mul_nonneg (sub_nonneg.mpr hη) (sub_nonneg.mpr hc.2)
    nlinarith
  · push_neg at he
    simpa only [height,he,zero_mul,Finset.sum_const_zero,add_zero] using hη

theorem height_eq_velocity_pairing {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} {θ : ℝ} (hi : χ i (normal θ)=1) :
    height χ v θ=dot (normal θ) (v i) := by
  rw [height_eq_single v hd (by rw [hi]; norm_num),hi]
  ring

/-- The actual angular derivative agrees with the velocity tangent pairing on
a whole cutoff plateau. -/
theorem height_hasDerivAt_corner {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} {θ : ℝ} (hi : ∀ᶠ w in 𝓝 (normal θ), χ i w=1) :
    HasDerivAt (height χ v) (dot (tangent θ) (v i)) θ := by
  have hc := normal_hasDerivAt θ
  have hdot := (gradientFunctional (v i)).hasFDerivAt.comp_hasDerivAt θ hc
  have hd' : HasDerivAt (fun φ => dot (normal φ) (v i)) (dot (tangent θ) (v i)) θ := by
    simpa only [gradientFunctional_apply,dot,mul_comm] using hdot
  apply hd'.congr_of_eventuallyEq
  filter_upwards [hc.continuousAt.eventually hi] with φ hφ
  exact height_eq_velocity_pairing v hd hφ

/-- Thus the joined field is exactly the actual corner velocity, on both sides
of a switching curve whenever its normals lie in the cutoff plateau. -/
theorem frame_eq_velocity {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hd : Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))))
    {i : Fin m} {θ : ℝ} (hi : ∀ᶠ w in 𝓝 (normal θ), χ i w=1) :
    frame χ v θ=v i := by
  exact angularFrame_eq_constant _ _ θ (v i)
    (height_eq_velocity_pairing v hd hi.self_of_nhds)
    (height_hasDerivAt_corner v hd hi).deriv

/-- Ambient smooth cutoffs yield a genuinely smooth angular height. -/
theorem height_contDiff {m : ℕ} {χ : Fin m → Vec 2 → ℝ} (v : Fin m → Vec 2)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) : ContDiff ℝ ∞ (height χ v) := by
  have hn : ContDiff ℝ ∞ normal := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Real.contDiff_cos
    · exact Real.contDiff_sin
  apply contDiff_const.add
  apply ContDiff.sum
  intro i _
  have hd : ContDiff ℝ ∞ (fun θ => dot (normal θ) (v i)) := by
    simpa only [gradientFunctional_apply,dot,mul_comm] using (gradientFunctional (v i)).contDiff.comp hn
  exact ((hχ i).comp hn).mul (hd.sub contDiff_const)

theorem height_periodic {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) :
    Function.Periodic (height χ v) (2*Real.pi) := by
  intro θ
  simp only [height,normal,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem height_deriv_periodic {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) :
    Function.Periodic (deriv (height χ v)) (2*Real.pi) := by
  intro θ
  rw [← deriv_comp_add_const]
  exact congrArg (fun f : ℝ → ℝ => deriv f θ) (funext (height_periodic χ v))

/-- The joined frame is periodic, so its value is independent of angular
representatives of the same normal direction. -/
theorem frame_periodic {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) :
    Function.Periodic (frame χ v) (2*Real.pi) := by
  intro θ
  simp only [frame,angularFrame,height_periodic χ v θ,height_deriv_periodic χ v θ,
    normal,tangent,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem frame_normal_pairing {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2) (θ : ℝ) :
    dot (normal θ) (frame χ v θ)=height χ v θ := normal_pairing_angularFrame _ _ θ

/-- Actual gradient visibility follows from its positive Euclidean length and
the derived positive height. -/
theorem frame_gradient_visibility {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → Vec 2)
    {θ c : ℝ} (hc : 0 < c) (hh : 0 < height χ v θ) :
    0 < dot (c • normal θ) (frame χ v θ) := by
  change 0 < dotProduct (c • normal θ) (frame χ v θ)
  rw [smul_dotProduct]
  change 0 < c*dot (normal θ) (frame χ v θ)
  rw [frame_normal_pairing]
  exact mul_pos hc hh

end PlanarJoinedFrame
end BfgsVerification
