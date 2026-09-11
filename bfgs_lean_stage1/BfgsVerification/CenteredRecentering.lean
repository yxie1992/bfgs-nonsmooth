import BfgsVerification.CenteredSmoothSublinear
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Metric Matrix

namespace BfgsVerification
namespace CenteredSmoothSublinear

/-- Optimality of the sum gives the homogeneous summand's supporting vector at
zero. Neither F nor gamma is required to be differentiable at the minimizer. -/
theorem center_support {n : ℕ} {F ψ γ : Vec n → ℝ}
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) {U : Set (Vec n)}
    (hU : IsOpen U) (hstar : star ∈ U)
    (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    {p : Vec n} (hp : HasFDerivAt ψ (gradientFunctional p) star) :
    Homogeneous.Supports γ 0 (-p) := by
  intro z
  let q : ℝ → ℝ := fun t => ψ (star + t • z) + t * γ z
  have ht : HasDerivAt (fun t : ℝ => star + t • z) z 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add star
  have hd : HasDerivAt q (dot p z + γ z) 0 := by
    have hcomp := hp.comp_hasDerivAt_of_eq 0 ht (by simp)
    simpa only [q, gradientFunctional_apply, one_mul] using
      hcomp.add ((hasDerivAt_id (0 : ℝ)).mul_const (γ z))
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, star + t • z ∈ U := by
    have hc : Continuous (fun t : ℝ => star + t • z) := by fun_prop
    have hh : Tendsto (fun t : ℝ => star + t • z) (𝓝 0) (𝓝 star) := by simpa using hc.tendsto 0
    exact hh.eventually (hU.mem_nhds hstar)
  have hlocal : IsLocalMinOn q (Ici 0) 0 := by
    filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with t ht0 htU
    have hm := hmin (star + t • z)
    rw [hrep star hstar, hrep _ htU, sub_self, Homogeneous.value_zero hhom] at hm
    have he : star + t • z - star = t • z := by abel
    rw [he, hhom t ht0 z] at hm
    simpa only [q, zero_smul, add_zero, zero_mul] using hm
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici 0) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Ici_self
  have hnonneg := hlocal.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hcone
  have hn : 0 ≤ dot p z + γ z := by simpa using hnonneg
  have hdot : dot (-p) (z - 0) = -dot p z := by
    change dotProduct (-p) (z - 0) = -dotProduct p z
    simp only [sub_zero, neg_dotProduct]
  rw [hdot, Homogeneous.value_zero hhom]
  linarith

/-- The smooth tangent is removed without changing the summed objective. -/
def smoothRemainder {n : ℕ} (ψ : Vec n → ℝ) (star p : Vec n) (x : Vec n) : ℝ :=
  ψ x - ψ star - dot p (x - star)

/-- The opposite linear term is added to the homogeneous summand. -/
def recenteredHomogeneous {n : ℕ} (γ : Vec n → ℝ) (p : Vec n) (z : Vec n) : ℝ :=
  γ z + dot p z

/-- Recentring preserves positive degree-one homogeneity. -/
theorem recentered_homogeneous {n : ℕ} {γ : Vec n → ℝ}
    (hγ : Homogeneous.PositiveDegreeOne γ) (p : Vec n) :
    Homogeneous.PositiveDegreeOne (recenteredHomogeneous γ p) := by
  intro t ht z
  unfold recenteredHomogeneous
  rw [hγ t ht z]
  have hd : dot p (t • z) = t * dot p z := dotProduct_smul _ _ _
  rw [hd]
  ring

/-- Recentring preserves convexity of the homogeneous summand. -/
theorem recentered_convex {n : ℕ} {γ : Vec n → ℝ}
    (hγ : ConvexOn ℝ univ γ) (p : Vec n) :
    ConvexOn ℝ univ (recenteredHomogeneous γ p) := by
  convert hγ.add ((gradientFunctional p).toLinearMap.convexOn convex_univ) using 1
  ext x
  change γ x + dot p x = γ x + (gradientFunctional p) x
  rw [gradientFunctional_apply]

/-- The adjusted smooth summand is convex on exactly the original domain. -/
theorem smoothRemainder_convex {n : ℕ} {ψ : Vec n → ℝ} {U : Set (Vec n)}
    (hψ : ConvexOn ℝ U ψ) (star p : Vec n) :
    ConvexOn ℝ U (smoothRemainder ψ star p) := by
  have hc := (hψ.sub ((gradientFunctional p).toLinearMap.concaveOn hψ.1)).add_const
    (dot p star - ψ star)
  convert hc using 1
  ext x
  change ψ x - ψ star - dot p (x - star) =
    (ψ x - (gradientFunctional p) x) + (dot p star - ψ star)
  rw [gradientFunctional_apply]
  have hd : dot p (x - star) = dot p x - dot p star := dotProduct_sub _ _ _
  rw [hd]
  ring

/-- Both adjusted summands are nonnegative and vanish at the center; their
sum is exactly the original objective minus its minimum on the original domain. -/
theorem centered_rewriting {n : ℕ} {F ψ γ : Vec n → ℝ}
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) {U : Set (Vec n)}
    (hU : IsOpen U) (hstar : star ∈ U) (hψ : ConvexOn ℝ U ψ)
    (hhom : Homogeneous.PositiveDegreeOne γ)
    (hrep : ∀ x ∈ U, F x = ψ x + γ (x - star))
    {p : Vec n} (hp : HasFDerivAt ψ (gradientFunctional p) star) :
    (∀ x ∈ U, 0 ≤ smoothRemainder ψ star p x) ∧
    smoothRemainder ψ star p star = 0 ∧
    (∀ z, 0 ≤ recenteredHomogeneous γ p z) ∧ recenteredHomogeneous γ p 0 = 0 ∧
    ∀ x ∈ U, F x - F star = smoothRemainder ψ star p x + recenteredHomogeneous γ p (x - star) := by
  have hs := center_support star hmin hU hstar hhom hrep hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hh := supporting_inequality_on hψ hp hstar hx
    simpa only [gradientFunctional_apply, smoothRemainder, sub_nonneg] using hh
  · simp [smoothRemainder, dot]
  · intro z
    have hh := hs z
    have hd : dot (-p) (z - 0) = -dot p z := by
      change dotProduct (-p) (z - 0) = -dotProduct p z
      simp only [sub_zero, neg_dotProduct]
    rw [hd, Homogeneous.value_zero hhom] at hh
    unfold recenteredHomogeneous
    linarith
  · simp [recenteredHomogeneous, Homogeneous.value_zero hhom, dot]
  · intro x hx
    rw [hrep x hx, hrep star hstar, sub_self, Homogeneous.value_zero hhom]
    unfold smoothRemainder recenteredHomogeneous
    ring


/-- Subtracting the smooth tangent changes the derivative by its fixed linear
functional, on the same domain. -/
theorem smoothRemainder_hasFDerivAt {n : ℕ} {ψ : Vec n → ℝ} (star p x : Vec n)
    {l : Vec n →L[ℝ] ℝ} (hl : HasFDerivAt ψ l x) :
    HasFDerivAt (smoothRemainder ψ star p) (l - gradientFunctional p) x := by
  have he : smoothRemainder ψ star p =
      fun z => ψ z - ψ star - (gradientFunctional p) z + dot p star := by
    ext z
    unfold smoothRemainder
    rw [gradientFunctional_apply]
    have hd : dot p (z - star) = dot p z - dot p star := dotProduct_sub _ _ _
    rw [hd]
    ring
  rw [he]
  exact ((hl.sub_const (ψ star)).sub (gradientFunctional p).hasFDerivAt).add_const (dot p star)

/-- Recentring preserves the original local C1,1 hypothesis, with no extension
of the smooth summand outside its original neighborhood. -/
theorem smoothRemainder_locallyC11 {n : ℕ} {ψ : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hψ : LocallyC11On U ψ) (star p : Vec n) :
    LocallyC11On U (smoothRemainder ψ star p) := by
  have hd : ∀ x ∈ U, HasFDerivAt (smoothRemainder ψ star p)
      (fderiv ℝ ψ x - gradientFunctional p) x := by
    intro x hx
    exact smoothRemainder_hasFDerivAt star p x
      ((hψ.1 x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have he : ∀ x ∈ U, fderiv ℝ (smoothRemainder ψ star p) x =
      fderiv ℝ ψ x - gradientFunctional p := fun x hx => (hd x hx).fderiv
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_⟩
  intro x hx
  obtain ⟨M, V, hV, hLip⟩ := hψ.2 hx
  refine ⟨M, V ∩ U, inter_mem hV self_mem_nhdsWithin, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro a ha b hb
  rw [he a ha.2, he b hb.2, dist_sub_right]
  exact hLip.dist_le_mul a ha.1 b hb.1

end CenteredSmoothSublinear
end BfgsVerification
