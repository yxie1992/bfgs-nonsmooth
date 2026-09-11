import BfgsVerification.RidgeProfiles

noncomputable section
open scoped Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification.RidgeSupersession

theorem midpoint_below_level {a b : ℝ → ℝ}
    (ha : StrictConvexOn ℝ univ a) (hb : StrictConvexOn ℝ univ b)
    {p q : ℝ} (hp : 0<p) (hq : 0<q) {x y : Vec 2} (hne : x≠y)
    {level : ℝ} (hx : objective a b p q x ≤ level) (hy : objective a b p q y ≤ level) :
    objective a b p q ((1/2 : ℝ) • x+(1/2 : ℝ) • y)<level := by
  have h0x := (le_max_left (a (x 0)+p*x 1) (b (x 0)-q*x 1)).trans hx
  have h1x := (le_max_right (a (x 0)+p*x 1) (b (x 0)-q*x 1)).trans hx
  have h0y := (le_max_left (a (y 0)+p*y 1) (b (y 0)-q*y 1)).trans hy
  have h1y := (le_max_right (a (y 0)+p*y 1) (b (y 0)-q*y 1)).trans hy
  change max (a ((1/2)*x 0+(1/2)*y 0)+p*((1/2)*x 1+(1/2)*y 1))
    (b ((1/2)*x 0+(1/2)*y 0)-q*((1/2)*x 1+(1/2)*y 1))<level
  apply max_lt_iff.mpr
  by_cases hu : x 0=y 0
  · have hv : x 1≠y 1 := by
      intro hv
      apply hne
      ext i
      fin_cases i <;> assumption
    have hm : (1/2 : ℝ)*x 0+(1/2)*y 0=x 0 := by rw [hu]; ring
    rw [hm]
    rw [← hu] at h0y h1y
    rcases lt_or_gt_of_ne hv with hv | hv
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · have hA := ha.2 (mem_univ (x 0)) (mem_univ (y 0)) hu
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    have hB := hb.2 (mem_univ (x 0)) (mem_univ (y 0)) hu
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    simp only [smul_eq_mul] at hA hB
    constructor <;> nlinarith

/-- No positive contour has a nontrivial straight boundary segment. The proof
uses strict horizontal profile convexity and both nonzero vertical slopes. -/
theorem strict_contours {a b : ℝ → ℝ}
    (ha : StrictConvexOn ℝ univ a) (hb : StrictConvexOn ℝ univ b)
    {p q : ℝ} (hp : 0<p) (hq : 0<q)
    (level : ℝ) (x y : Vec 2)
    (hseg : segment ℝ x y⊆frontier {z | objective a b p q z ≤ level}) : x=y := by
  have hc := convex_continuous (objective_convex ha.convexOn hb.convexOn p q)
  have he (z : Vec 2) (hz : z∈segment ℝ x y) : objective a b p q z=level :=
    frontier_le_subset_eq hc continuous_const (hseg hz)
  have hx := he x (left_mem_segment ℝ x y)
  have hy := he y (right_mem_segment ℝ x y)
  by_contra hne
  have hmid := midpoint_below_level ha hb hp hq hne hx.le hy.le
  have hm : (1/2 : ℝ) • x+(1/2 : ℝ) • y∈segment ℝ x y :=
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  exact (ne_of_lt hmid) (he _ hm)

end BfgsVerification.RidgeSupersession
