import BfgsVerification.SemialgebraicGraphs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.Equiv

/-! A proved parameter-preserving local inverse and scalar implicit root graph.
The only nondegeneracy input is the actual nonzero vertical derivative. -/
noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

def rootAugment (F : Vec n × ℝ → ℝ) (z : Vec n × ℝ) : Vec n × ℝ := (z.1,F z)

theorem linear_vertical (D : Vec n × ℝ →L[ℝ] ℝ) (t : ℝ) :
    D (0,t) = t * D (0,1) := by
  have he : ((0,t) : Vec n × ℝ) = t • ((0,1) : Vec n × ℝ) := by simp
  rw [he,map_smul]
  rfl

theorem rootAugment_derivative_injective (D : Vec n × ℝ →L[ℝ] ℝ)
    (hD : D (0,1) ≠ 0) : Function.Injective ((ContinuousLinearMap.fst ℝ (Vec n) ℝ).prod D) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨x,t⟩ hz
  have hx := congrArg Prod.fst hz
  have ht := congrArg Prod.snd hz
  change x = 0 at hx
  change D (x,t) = 0 at ht
  rw [hx,linear_vertical] at ht
  have ht0 : t = 0 := (mul_eq_zero.mp ht).resolve_right hD
  simp [hx,ht0]

def rootAugmentEquiv (D : Vec n × ℝ →L[ℝ] ℝ) (hD : D (0,1) ≠ 0) :
    (Vec n × ℝ) ≃L[ℝ] (Vec n × ℝ) :=
  (LinearEquiv.ofInjectiveEndo ((ContinuousLinearMap.fst ℝ (Vec n) ℝ).prod D).toLinearMap
    (rootAugment_derivative_injective D hD)).toContinuousLinearEquiv

theorem rootAugmentEquiv_apply (D : Vec n × ℝ →L[ℝ] ℝ) (hD : D (0,1) ≠ 0)
    (z : Vec n × ℝ) : rootAugmentEquiv D hD z = (z.1,D z) := rfl

/-- The root function and its local uniqueness are derived by the actual inverse
function theorem, with no root selector assumed. -/
theorem exists_smooth_root_germ {F : Vec n × ℝ → ℝ} {a : Vec n} {b : ℝ}
    {k : WithTop ℕ∞} (hk : 1 ≤ k) (hF : ContDiffAt ℝ k F (a,b))
    (hzero : F (a,b) = 0) (hD : fderiv ℝ F (a,b) (0,1) ≠ 0) :
    ∃ g : Vec n → ℝ, g a = b ∧ ContDiffAt ℝ k g a ∧
      (∀ᶠ x in 𝓝 a, F (x,g x) = 0) ∧
      ∀ᶠ z : Vec n × ℝ in 𝓝 (a,b), F z = 0 → z.2 = g z.1 := by
  let D := fderiv ℝ F (a,b)
  let E := rootAugmentEquiv D hD
  have hfd := (hF.differentiableAt hk).hasFDerivAt
  have hd : HasFDerivAt (rootAugment F) E.toContinuousLinearMap (a,b) :=
    ((ContinuousLinearMap.fst ℝ (Vec n) ℝ).hasFDerivAt).prodMk hfd
  have hc : ContDiffAt ℝ k (rootAugment F) (a,b) := contDiffAt_fst.prodMk hF
  have hz : rootAugment F (a,b) = (a,0) := by simp [rootAugment,hzero]
  let I := hc.localInverse hd hk
  have hI0 : I (a,0) = (a,b) := by simpa only [hz] using hc.localInverse_apply_image hd hk
  have hIc : ContDiffAt ℝ k I (a,0) := by simpa only [hz] using hc.to_localInverse hd hk
  have hIr : ∀ᶠ z : Vec n × ℝ in 𝓝 (a,0), rootAugment F (I z) = z := by
    simpa only [hz] using (hc.hasStrictFDerivAt' hd hk).eventually_right_inverse
  have hIl : ∀ᶠ z : Vec n × ℝ in 𝓝 (a,b), I (rootAugment F z) = z :=
    (hc.hasStrictFDerivAt' hd hk).eventually_left_inverse
  let g : Vec n → ℝ := fun x => (I (x,0)).2
  refine ⟨g,congrArg Prod.snd hI0,?_,?_,?_⟩
  · exact (hIc.comp a (contDiffAt_id.prodMk contDiffAt_const)).snd
  · filter_upwards [((ContinuousLinearMap.inl ℝ (Vec n) ℝ).continuous.tendsto a).eventually hIr] with x hx
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    change (I (x,0)).1 = x at h1
    change F (I (x,0)) = 0 at h2
    have he : I (x,0) = (x,g x) := Prod.ext h1 rfl
    rwa [he] at h2
  · filter_upwards [hIl] with z hz hroot
    have he : rootAugment F z = (z.1,0) := by simp [rootAugment,hroot]
    rw [he] at hz
    exact (congrArg Prod.snd hz).symm

end RealAlgebraicGeometry
end BfgsVerification
