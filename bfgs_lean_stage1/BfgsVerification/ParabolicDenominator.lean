import BfgsVerification.ParabolicDenominatorAlgebra

/-! Uniform, actual eligible-pair denominator bounds for Q. No normal slope,
horizontal coordinate, or displacement is assumed nonzero. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Set
namespace BfgsVerification
namespace Parabolic
namespace Family
open TransportedCertificate
variable {m : ℕ} (P : Family m)

def maxQuadratic : ℝ := Finset.univ.sup' P.indices_nonempty P.a

theorem le_maxQuadratic (i : Fin m) : P.a i ≤ P.maxQuadratic :=
  Finset.le_sup' P.a (Finset.mem_univ i)

theorem maxQuadratic_pos : 0 < P.maxQuadratic := by
  obtain ⟨i, _⟩ := P.positive_slope
  exact (P.a_pos i).trans_le (P.le_maxQuadratic i)

theorem radial_error_bound {i j : Fin m} {x z : Vec 2} {G R d : ℝ}
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hd : 0 ≤ d) (hz : |z 0| ≤ R)
    (hg : |P.branchGradient i x 0| ≤ G) (hh : |P.branchGradient j z 0| ≤ G)
    (he : P.deficit i z ≤ d) :
    |2 * P.a i * horizontalStep x z * z 0 + 2 * P.deficit i z +
      (P.branchGradient j z 0 - P.branchGradient i x 0) * horizontalStep x z| ≤
      (2 * P.maxQuadratic * R + 2 * G + 2) * (|horizontalStep x z| + d) := by
  have hA := P.maxQuadratic_pos
  have hdiff : |P.branchGradient j z 0 - P.branchGradient i x 0| ≤ 2*G :=
    (abs_sub _ _).trans (by linarith)
  have hterm : |2 * P.a i * horizontalStep x z * z 0| ≤
      2 * P.maxQuadratic * R * |horizontalStep x z| := by
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos (P.a_pos i)]
    have hmul := mul_le_mul (P.le_maxQuadratic i) hz (abs_nonneg _) P.maxQuadratic_pos.le
    nlinarith [mul_le_mul_of_nonneg_right hmul (abs_nonneg (horizontalStep x z))]
  have heterm : |2*P.deficit i z| ≤ 2*d := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (P.deficit_nonneg i z))]
    linarith
  have hyd : |(P.branchGradient j z 0 - P.branchGradient i x 0) * horizontalStep x z| ≤
      2*G*|horizontalStep x z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
  have hsum := (abs_add
    (2 * P.a i * horizontalStep x z * z 0 + 2 * P.deficit i z)
    ((P.branchGradient j z 0 - P.branchGradient i x 0) * horizontalStep x z)).trans
      (add_le_add_right ((abs_add _ _).trans (add_le_add hterm heterm)) _)
  have hp : 0 ≤ (2 * P.maxQuadratic * R + 2 * G) * d := by positivity
  nlinarith [abs_nonneg (horizontalStep x z)]

/-- Q.13 with constants selected before every eligible pair in the compact set.
The positive level is imposed at the old endpoint; the theorem does not require
adjacent active branches, a nonzero b_i, or a small normal displacement. -/
theorem exists_small_denominator_bounds {K : Set (Vec 2)} (hK : IsCompact K)
    {η c₁ c₂ : ℝ} (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ x ∈ K, ∀ z ∈ K, ∀ g h : Vec 2,
        EligiblePair P.objective c₁ c₂ x z g h → η ≤ P.objective x →
        pairDecrease x z g ≤ δ →
        pairDecrease x z g ≤ C * |stepDeterminant x z| ∧
        |horizontalStep x z| ≤ C * |stepDeterminant x z| ∧ stepDeterminant x z ≠ 0 := by
  obtain ⟨R, hR, hrad⟩ := compact_sqNorm_radius hK (0 : Vec 2)
  obtain ⟨G, hG, hgrad⟩ := convex_supporting_bound_on_compact P.objective_convex hK
  let E := 2 * P.maxQuadratic * R + 2 * G + 2
  let κ := 1-c₂
  let τ := η*κ/(4*E)
  let δ := min (η/2) (min (P.minQuadratic * τ^2) τ)
  let Cd := 2*(4*G^2)/(η*κ)
  let Ch := (G+R*Cd)/(2*η)
  have hA := P.maxQuadratic_pos
  have hκ : 0 < κ := sub_pos.mpr hc₂
  have hE : 0 < E := by dsimp [E]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min (by positivity) (lt_min (mul_pos P.minQuadratic_pos (sq_pos_of_pos hτ)) hτ)
  have hCd : 0 < Cd := by dsimp [Cd]; positivity
  refine ⟨max Cd Ch, δ, hCd.trans_le (le_max_left _ _), hδ, ?_⟩
  intro x hx z hz g h hp hFx hdδ
  obtain ⟨i, hi, hgi⟩ := P.gradient_from_active hp.gradient_x
  obtain ⟨j, hj, hhj⟩ := P.gradient_from_active hp.gradient_z
  have hg (l : Fin 2) : |g l| ≤ G := abs_coordinate_of_sqNorm_le hG.le
    (hgrad x hx g (convex_supporting_inequality P.objective_convex hp.gradient_x)) l
  have hh (l : Fin 2) : |h l| ≤ G := abs_coordinate_of_sqNorm_le hG.le
    (hgrad z hz h (convex_supporting_inequality P.objective_convex hp.gradient_z)) l
  have hr (v : Vec 2) (hv : v ∈ K) : |v 0| ≤ R :=
    abs_coordinate_of_sqNorm_le hR.le (by simpa only [sub_zero] using hrad v hv) 0
  let d := pairDecrease x z g
  let t := pairCurvature x z g h
  let err := 2 * P.a i * horizontalStep x z * z 0 + 2 * P.deficit i z +
    (h 0-g 0) * horizontalStep x z
  have hd : 0 < d := hp.decrease_pos
  have he : P.deficit i z ≤ d := P.eligible_deficit_le hc₁ hi hp
  have herr : |err| ≤ E*(|horizontalStep x z|+d) := by
    simpa only [err, E, hgi, hhj] using P.radial_error_bound hG.le hR.le hd.le (hr z hz)
      (by rw [← hgi]; exact hg 0) (by rw [← hhj]; exact hh 0) he
  have hdet : |determinant g (h-g)| ≤ 4*G^2 := determinant_gradient_bound hG.le hg hh
  have hident := P.determinant_identity (j := j) (z := z) hi
  rw [← hgi, ← hhj] at hident
  have hold := P.old_radial_identity (i := i) (x := x) hj
  rw [← hgi, ← hhj] at hold
  change dot (h-g) (radialDirection x) = -2*t+err at hold
  rw [hold] at hident
  have hmain : (2*P.objective x-2*d)*t ≤ 4*G^2*|stepDeterminant x z| + E*d*(|horizontalStep x z|+d) := by
    have heq : (2*P.objective x-2*d)*t = -determinant g (h-g)*stepDeterminant x z-d*err := by
      change determinant g (h-g)*stepDeterminant x z = -d*(-2*t+err)-2*P.objective x*t at hident
      nlinarith [hident]
    rw [heq]
    have h1 : -determinant g (h-g)*stepDeterminant x z ≤ 4*G^2*|stepDeterminant x z| := by
      calc
        -determinant g (h-g)*stepDeterminant x z ≤ |determinant g (h-g)*stepDeterminant x z| := by
          simpa only [neg_mul] using neg_le_abs (determinant g (h-g)*stepDeterminant x z)
        _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hdet (abs_nonneg _)
    have h2 : -(d*err) ≤ E*d*(|horizontalStep x z|+d) := by
      calc
        -(d*err) ≤ |d*err| := neg_le_abs _
        _ = d*|err| := by rw [abs_mul, abs_of_pos hd]
        _ ≤ d*(E*(|horizontalStep x z|+d)) := mul_le_mul_of_nonneg_left herr hd.le
        _ = _ := by ring
    linarith
  have hdη : d ≤ η/2 := hdδ.trans (min_le_left _ _)
  have hda : d ≤ P.minQuadratic*τ^2 := hdδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdτ : d ≤ τ := hdδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdD : d ≤ Cd*|stepDeterminant x z| :=
    denominator_absorption hη hκ hE P.minQuadratic_pos hd hp.curvature hFx hdη hda hdτ
      (P.eligible_horizontal_sq_le hc₁ hi hp) hmain
  have hb : |P.b i| ≤ G := by simpa only [hgi, branchGradient, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hg 1
  have hhid := P.slope_determinant_identity (z := z) hi
  rw [← hgi] at hhid
  have hhD : |horizontalStep x z| ≤ Ch*|stepDeterminant x z| :=
    horizontal_from_determinant hη hFx hd.le hb (hr x hx) hR.le hdD hhid
  refine ⟨hdD.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)),
    hhD.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)), ?_⟩
  intro heq
  rw [heq, abs_zero, mul_zero] at hdD
  exact (not_le_of_gt hd) hdD

end Family
end Parabolic
end BfgsVerification
