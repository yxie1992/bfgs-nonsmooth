import BfgsVerification.SemialgebraicGraphs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-! Actual finite root boundaries and sign constancy for finitely many real
univariate polynomials. No projection or cell decomposition is assumed. -/
noncomputable section
open Set Polynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- The real roots of all nonzero polynomials in the finite family. The zero
polynomial contributes no boundary; its sign is constant everywhere. -/
def rootBoundary (P : Finset (Polynomial ℝ)) : Finset ℝ :=
  P.biUnion (fun p => p.roots.toFinset)

theorem mem_rootBoundary {P : Finset (Polynomial ℝ)} {p : Polynomial ℝ}
    (hp : p ∈ P) (hne : p ≠ 0) {x : ℝ} (hx : p.eval x = 0) : x ∈ rootBoundary P := by
  classical
  exact Finset.mem_biUnion.mpr ⟨p,hp,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hx)⟩

/-- On a closed interval avoiding the actual finite root boundary, every
polynomial in the family has fixed equality-to-zero and positive-sign tests. -/
theorem polynomial_sign_constant_on_gap {P : Finset (Polynomial ℝ)}
    {p : Polynomial ℝ} (hp : p ∈ P) {x y : ℝ} (hxy : x ≤ y)
    (hgap : ∀ z ∈ Icc x y, z ∉ rootBoundary P) :
    (p.eval x = 0 ↔ p.eval y = 0) ∧ (0 < p.eval x ↔ 0 < p.eval y) := by
  by_cases hzero : p = 0
  · simp [hzero]
  have hn (z : ℝ) (hz : z ∈ Icc x y) : p.eval z ≠ 0 :=
    fun he => hgap z hz (mem_rootBoundary hp hzero he)
  have hx := hn x (left_mem_Icc.mpr hxy)
  have hy := hn y (right_mem_Icc.mpr hxy)
  refine ⟨by simp [hx,hy], ?_⟩
  constructor
  · intro hpx
    by_contra hpy
    have hle : p.eval y ≤ 0 := le_of_not_gt hpy
    obtain ⟨z,hz,hz0⟩ := (intermediate_value_Icc' hxy p.continuous.continuousOn)
      (show (0 : ℝ) ∈ Icc (p.eval y) (p.eval x) from ⟨hle,hpx.le⟩)
    exact hn z hz hz0
  · intro hpy
    by_contra hpx
    have hle : p.eval x ≤ 0 := le_of_not_gt hpx
    obtain ⟨z,hz,hz0⟩ := (intermediate_value_Icc hxy p.continuous.continuousOn)
      (show (0 : ℝ) ∈ Icc (p.eval x) (p.eval y) from ⟨hle,hpy.le⟩)
    exact hn z hz hz0

/-- A finite cut profile labels every root-free interval, without choosing or
assuming an enumeration of the roots. -/
def cutProfile (B : Finset ℝ) (x : ℝ) : Finset ℝ := B.filter (fun b => b < x)

theorem gap_of_equal_cutProfile {B : Finset ℝ} {x y : ℝ}
    (hxy : x ≤ y) (hy : y ∉ B) (hprofile : cutProfile B x = cutProfile B y) :
    ∀ z ∈ Icc x y, z ∉ B := by
  intro z hz hzb
  have hzy : z < y := lt_of_le_of_ne hz.2 (fun he => hy (he ▸ hzb))
  have hmem : z ∈ cutProfile B y := Finset.mem_filter.mpr ⟨hzb,hzy⟩
  rw [← hprofile] at hmem
  exact (not_lt_of_ge hz.1) (Finset.mem_filter.mp hmem).2

/-- Sign constancy for any two points with the same actual finite root-cut
profile. Endpoints may occur in either order. -/
theorem polynomial_sign_constant_on_profile {P : Finset (Polynomial ℝ)}
    {p : Polynomial ℝ} (hp : p ∈ P) {x y : ℝ}
    (hx : x ∉ rootBoundary P) (hy : y ∉ rootBoundary P)
    (hprofile : cutProfile (rootBoundary P) x = cutProfile (rootBoundary P) y) :
    (p.eval x = 0 ↔ p.eval y = 0) ∧ (0 < p.eval x ↔ 0 < p.eval y) := by
  rcases le_total x y with hxy | hyx
  · exact polynomial_sign_constant_on_gap hp hxy (gap_of_equal_cutProfile hxy hy hprofile)
  · have h := polynomial_sign_constant_on_gap hp hyx (gap_of_equal_cutProfile hyx hx hprofile.symm)
    exact ⟨h.1.symm,h.2.symm⟩

end RealAlgebraicGeometry
end BfgsVerification
