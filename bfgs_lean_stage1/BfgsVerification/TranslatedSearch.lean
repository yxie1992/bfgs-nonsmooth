import BfgsVerification.TranslatedLocalModel
import BfgsVerification.FiniteSearchTransfer

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.TranslatedRun
open DeterministicLineSearch

variable {n : ℕ} {Q F : Vec n → ℝ}

theorem translated_trial (p x d : Vec n) (t a : ℝ) :
    (p+t • x)+a • (t • d)=p+t • (x+a • d) := by
  rw [smul_add,smul_comm a t]
  abel

theorem translated_comparisons {p x d g : Vec n} {t A a c₁ c₂ : ℝ} (ht : t≠0)
    (hbase : F (p+t • x)=A+t^2*Q x)
    (htrial : F (p+t • (x+a • d))=A+t^2*Q (x+a • d))
    (hgrad : coordinateGradient F (p+t • (x+a • d))=t • coordinateGradient Q (x+a • d)) :
    (Armijo F (p+t • x) (t • d) (t • g) c₁ a↔Armijo Q x d g c₁ a) ∧
    (Wolfe F (p+t • x) (t • d) (t • g) c₂ a↔Wolfe Q x d g c₂ a) := by
  have hs : 0<t^2 := sq_pos_of_ne_zero ht
  have hp (v : Vec n) : dot (t • v) (t • d)=t^2*dot v d := by
    rw [dot_smul_right,PlanarUpdate.dot_scale_left]
    ring
  constructor
  · simp only [Armijo,translated_trial,hbase,htrial,hp]
    change A+t^2*Q (x+a • d)<A+t^2*Q x+c₁*a*(t^2*dot g d)↔_
    have he : A+t^2*Q x+c₁*a*(t^2*dot g d)=A+t^2*(Q x+c₁*a*dot g d) := by ring
    rw [he,add_lt_add_iff_left,mul_lt_mul_left hs]
  · simp only [Wolfe,translated_trial,hgrad,hp]
    rw [show c₂*(t^2*dot g d)=t^2*(c₂*dot g d) from by ring,mul_lt_mul_left hs]

theorem translated_query_gradient {U : Set (Vec n)} (hU : IsOpen U)
    {p z g : Vec n} {t A : ℝ} (ht : t≠0) (hz : z∈U)
    (hmodel : ∀y∈U,F (p+t • y)=A+t^2*Q y)
    (hg : HasFDerivAt Q (gradientFunctional g) z) :
    coordinateGradient F (p+t • z)=t • coordinateGradient Q z := by
  rw [actual_coordinateGradient hg]
  exact actual_coordinateGradient (local_model_hasGradient hU ht hz hmodel hg)

/-- Local identity and actual differentiability are required only at the
accepted base and the source search's actually attempted points. -/
theorem local_model_search {U : Set (Vec n)} (hU : IsOpen U)
    {p x g : Vec n} {H : Mat n} {t A c₁ c₂ : ℝ} (ht : t≠0) (hx : x∈U)
    (hg : HasFDerivAt Q (gradientFunctional g) x) (fuel : ℕ)
    (hmodel : ∀y∈U,F (p+t • y)=A+t^2*Q y)
    (hqueries : ∀a∈(fromMetric Q x H c₁ c₂ fuel).2,
      x+a • bfgsStep H g 1∈U ∧ DifferentiableAt ℝ Q (x+a • bfgsStep H g 1)) :
    fromMetric F (p+t • x) H c₁ c₂ fuel=fromMetric Q x H c₁ c₂ fuel := by
  have hgf := local_model_hasGradient hU ht hx hmodel hg
  have hcg := actual_coordinateGradient hg
  have hcf := actual_coordinateGradient hgf
  unfold fromMetric
  rw [hcg,hcf,bfgsStep_scale_gradient]
  apply search_history_congr
  intro a ha
  have hmem : a∈(fromMetric Q x H c₁ c₂ fuel).2 := by
    simpa only [fromMetric,hcg] using ha
  obtain ⟨hq,hd⟩ := hqueries a hmem
  exact translated_comparisons ht (hmodel x hx) (hmodel _ hq)
    (translated_query_gradient hU ht hq hmodel (hasFDerivAt_coordinateGradient hd))

end BfgsVerification.TranslatedRun
