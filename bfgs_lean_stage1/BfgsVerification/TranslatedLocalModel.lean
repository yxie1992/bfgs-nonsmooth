import BfgsVerification.TranslatedRun
import BfgsVerification.DEmbeddingObjective

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.TranslatedRun

variable {n : ℕ} {Q F : Vec n → ℝ}

theorem local_model_hasGradient {U : Set (Vec n)} (hU : IsOpen U)
    {p x g : Vec n} {t A : ℝ} (ht : t≠0) (hx : x∈U)
    (hmodel : ∀y∈U,F (p+t • y)=A+t^2*Q y)
    (hg : HasFDerivAt Q (gradientFunctional g) x) :
    HasFDerivAt F (gradientFunctional (t • g)) (p+t • x) := by
  let invmap : Vec n → Vec n := fun z => t⁻¹ • (z-p)
  have hi : invmap (p+t • x)=x := by simp [invmap,smul_smul,ht]
  have hid : HasFDerivAt invmap (t⁻¹ • ContinuousLinearMap.id ℝ (Vec n)) (p+t • x) := by
    exact ((hasFDerivAt_id (p+t • x)).sub_const p).const_smul t⁻¹
  have hg1 : HasFDerivAt Q (gradientFunctional g) (invmap (p+t • x)) := hi.symm ▸ hg
  have hcomp := hg1.comp (p+t • x) hid
  have hf : HasFDerivAt (fun z => A+t^2*Q (invmap z))
      (gradientFunctional (t • g)) (p+t • x) := by
    convert (hcomp.const_mul (t^2)).const_add A using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul,gradientFunctional_apply,
      dot_smul_right,DEmbedding.gradientFunctional_smul]
    field_simp [ht]
    <;> ring
  apply hf.congr_of_eventuallyEq
  have hnear : ∀ᶠ z in 𝓝 (p+t • x),invmap z∈U := by
    have hc : Continuous invmap := continuous_const.smul (continuous_id.sub continuous_const)
    apply hc.continuousAt.eventually
    rw [hi]
    exact hU.mem_nhds hx
  filter_upwards [hnear] with z hz
  have hm := hmodel (invmap z) hz
  have he : p+t • invmap z=z := by simp [invmap,smul_smul,ht]
  rw [he] at hm
  exact hm

theorem data_of_local_model {R : AdmissibleBFGSRun n Q} {U : Set (Vec n)} (hU : IsOpen U)
    {p : Vec n} {t A : ℝ} (ht : t≠0) (hF : ConvexOn ℝ univ F)
    (hx : ∀k,R.x k∈U) (hmodel : ∀y∈U,F (p+t • y)=A+t^2*Q y) :
    Data R F p t A where
  convex := hF
  value k := hmodel (R.x k) (hx k)
  hasGradient k := local_model_hasGradient hU ht (hx k) hmodel (R.hasGradient k)

end BfgsVerification.TranslatedRun
