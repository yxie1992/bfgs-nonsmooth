import BfgsVerification.ConvexSubdifferential
import BfgsVerification.FiniteRayLineSearch
import BfgsVerification.QuadraticCellRadial

/-! Actual two-slope affine residual penalties, including abs/hinge/quantile.
Developed after the seventh milestone with actual compiler feedback. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineKinks

structure Kink (n : ℕ) where
  a : Vec n
  b : ℝ
  lo : ℝ
  hi : ℝ
  ordered : lo ≤ hi

namespace Kink
variable {n : ℕ} (P : Kink n)

def residual (x : Vec n) : ℝ := dot P.a x-P.b
def value (x : Vec n) : ℝ := max (P.lo*P.residual x) (P.hi*P.residual x)

theorem residual_hasGradient (x : Vec n) :
    HasFDerivAt P.residual (gradientFunctional P.a) x := by
  convert ((gradientFunctional P.a).hasFDerivAt (x := x)).sub_const P.b using 1
  ext z
  simp [residual,gradientFunctional_apply]

theorem scaled_residual_hasGradient (c : ℝ) (x : Vec n) :
    HasFDerivAt (fun z => c*P.residual z) (gradientFunctional (c • P.a)) x := by
  convert (P.residual_hasGradient x).const_mul c using 1
  ext z
  simp [gradientFunctional_apply,dot,Finset.mul_sum,mul_assoc]

theorem residual_affine (x z : Vec n) {a b : ℝ} (hab : a+b=1) :
    P.residual (a • x+b • z)=a*P.residual x+b*P.residual z := by
  unfold residual
  change P.a ⬝ᵥ (a • x+b • z)-P.b=a*(P.a ⬝ᵥ x-P.b)+b*(P.a ⬝ᵥ z-P.b)
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
  simp only [smul_eq_mul]
  linear_combination P.b*hab

theorem value_convex : ConvexOn ℝ univ P.value := by
  have hc (c : ℝ) : ConvexOn ℝ univ (fun x => c*P.residual x) := by
    refine ⟨convex_univ,?_⟩
    intro x hx z hz a b ha hb hab
    change c*P.residual (a • x+b • z) ≤ a*(c*P.residual x)+b*(c*P.residual z)
    apply le_of_eq
    rw [P.residual_affine x z hab]
    ring
  exact (hc P.lo).sup (hc P.hi)

theorem value_hasGradient_pos {x : Vec n} (hx : 0 < P.residual x) :
    HasFDerivAt P.value (gradientFunctional (P.hi • P.a)) x := by
  apply (P.scaled_residual_hasGradient P.hi x).congr_of_eventuallyEq
  have hc : Continuous P.residual := by unfold residual dot; fun_prop
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hx] with z hz
  exact max_eq_right (mul_le_mul_of_nonneg_right P.ordered hz.le)

theorem value_hasGradient_neg {x : Vec n} (hx : P.residual x < 0) :
    HasFDerivAt P.value (gradientFunctional (P.lo • P.a)) x := by
  apply (P.scaled_residual_hasGradient P.lo x).congr_of_eventuallyEq
  have hc : Continuous P.residual := by unfold residual dot; fun_prop
  filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hx] with z hz
  exact max_eq_left (mul_le_mul_of_nonpos_right P.ordered hz.le)

theorem residual_sub (x z : Vec n) : P.residual z-P.residual x=dot P.a (z-x) := by
  unfold residual
  change P.a ⬝ᵥ z-P.b-(P.a ⬝ᵥ x-P.b)=P.a ⬝ᵥ (z-x)
  rw [dotProduct_sub]
  ring

theorem lo_support_at_zero {x : Vec n} (hx : P.residual x=0) :
    Homogeneous.Supports P.value x (P.lo • P.a) := by
  intro z
  have hv : P.value x=0 := by simp [value,hx]
  rw [hv,sub_zero]
  change (P.lo • P.a) ⬝ᵥ (z-x) ≤ _
  rw [smul_dotProduct]
  change P.lo*dot P.a (z-x) ≤ _
  rw [← P.residual_sub,hx,sub_zero]
  exact le_max_left _ _

theorem hi_support_at_zero {x : Vec n} (hx : P.residual x=0) :
    Homogeneous.Supports P.value x (P.hi • P.a) := by
  intro z
  have hv : P.value x=0 := by simp [value,hx]
  rw [hv,sub_zero]
  change (P.hi • P.a) ⬝ᵥ (z-x) ≤ _
  rw [smul_dotProduct]
  change P.hi*dot P.a (z-x) ≤ _
  rw [← P.residual_sub,hx,sub_zero]
  exact le_max_right _ _

theorem differentiable_of_trivial (x : Vec n) (htr : P.a=0 ∨ P.lo=P.hi) :
    DifferentiableAt ℝ P.value x := by
  rcases htr with ha | he
  · have hv : P.value=(fun _ => max (P.lo*(-P.b)) (P.hi*(-P.b))) := by
      ext z
      simp [value,residual,ha,dot]
    rw [hv]
    exact differentiableAt_const _
  · have hv : P.value=(fun z => P.lo*P.residual z) := by ext z; simp [value,he]
    rw [hv]
    exact (P.scaled_residual_hasGradient P.lo x).differentiableAt

theorem differentiable_of_residual_ne_zero {x : Vec n} (hx : P.residual x ≠ 0) :
    DifferentiableAt ℝ P.value x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · exact (P.value_hasGradient_neg hn).differentiableAt
  · exact (P.value_hasGradient_pos hp).differentiableAt

end Kink

theorem sum_supports {n : ℕ} {ι : Type*} [Fintype ι]
    {f : ι → Vec n → ℝ} {x : Vec n} {g : ι → Vec n}
    (hg : ∀ i, Homogeneous.Supports (f i) x (g i)) :
    Homogeneous.Supports (fun z => ∑ i, f i z) x (∑ i, g i) := by
  intro z
  simp only [dot,Finset.sum_apply,Finset.sum_mul,← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun i _ => hg i z)

/-- Differentiability of the whole finite convex sum forces uniqueness of each
component's supporting vector. No component differentiability is assumed. -/
theorem sum_component_supports_equal {n : ℕ} {ι : Type*} [Fintype ι]
    {f : ι → Vec n → ℝ} (hf : ∀ i, ConvexOn ℝ univ (f i)) {x : Vec n}
    (hd : DifferentiableAt ℝ (fun z => ∑ i, f i z) x) (i : ι) {a b : Vec n}
    (ha : Homogeneous.Supports (f i) x a) (hb : Homogeneous.Supports (f i) x b) : a=b := by
  classical
  choose g hg using fun j => ConvexSubdifferential.subdifferential_nonempty (hf j) x
  have hsup (c : Vec n) (hc : Homogeneous.Supports (f i) x c) :
      Homogeneous.Supports (fun z => ∑ j, f j z) x (∑ j, Function.update g i c j) := by
    apply sum_supports
    intro j
    by_cases he : j=i
    · subst j
      simpa using hc
    · simpa [Function.update_of_ne he] using hg j
  have he := (supporting_vector_eq_gradient (hsup a ha) (hasFDerivAt_coordinateGradient hd)).trans
    (supporting_vector_eq_gradient (hsup b hb) (hasFDerivAt_coordinateGradient hd)).symm
  simp only [Finset.sum_update_of_mem (Finset.mem_univ i)] at he
  exact add_right_cancel he


def penalty {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n) (x : Vec n) : ℝ :=
  ∑ i, (P i).value x

theorem penalty_convex {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n) :
    ConvexOn ℝ univ (penalty P) := by
  refine ⟨convex_univ,?_⟩
  intro x hx z hz a b ha hb hab
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (P i).value_convex.2 hx hz ha hb hab)
  simpa only [penalty,smul_eq_mul,Finset.sum_add_distrib,Finset.mul_sum] using h

/-- Every genuine kink has nonzero initial residual at a differentiable point
of the whole penalty. This discharges the degenerate-ray case from actual data. -/
theorem initial_residual_ne_zero {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n)
    {x : Vec n} (hd : DifferentiableAt ℝ (penalty P) x) (i : ι)
    (ha : (P i).a ≠ 0) (hl : (P i).lo < (P i).hi) : (P i).residual x ≠ 0 := by
  intro hz
  have he := sum_component_supports_equal (fun j => (P j).value_convex) hd i
    ((P i).lo_support_at_zero hz) ((P i).hi_support_at_zero hz)
  have hzero : ((P i).lo-(P i).hi) • (P i).a=0 := by rw [sub_smul,he,sub_self]
  exact ha ((smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hl.ne))

theorem residual_on_ray {n : ℕ} (P : Kink n) (x p : Vec n) (t : ℝ) :
    P.residual (x+t • p)=P.residual x+t*dot P.a p := by
  unfold Kink.residual
  change P.a ⬝ᵥ (x+t • p)-P.b=P.a ⬝ᵥ x-P.b+t*(P.a ⬝ᵥ p)
  rw [dotProduct_add,dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- The actual full-space bad-time set is finite, including rays parallel to
some kink hyperplanes. Only actual initial differentiability is required. -/
theorem penalty_finite_bad_ray {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n)
    {x : Vec n} (hd : DifferentiableAt ℝ (penalty P) x) (p : Vec n) :
    {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ (penalty P) (x+t • p)}.Finite := by
  classical
  apply (Set.finite_range (fun i => -(P i).residual x / dot (P i).a p)).subset
  intro t ht
  by_contra hn
  have hc (i : ι) : DifferentiableAt ℝ (P i).value (x+t • p) := by
    by_cases ha : (P i).a=0
    · exact (P i).differentiable_of_trivial _ (Or.inl ha)
    by_cases hl : (P i).lo=(P i).hi
    · exact (P i).differentiable_of_trivial _ (Or.inr hl)
    have hlt : (P i).lo < (P i).hi := lt_of_le_of_ne (P i).ordered hl
    apply (P i).differentiable_of_residual_ne_zero
    intro hz
    have hstart := initial_residual_ne_zero P hd i ha hlt
    have he := residual_on_ray (P i) x p t
    have hp : dot (P i).a p ≠ 0 := by
      intro he0
      rw [he0,mul_zero,add_zero,hz] at he
      exact hstart he.symm
    have hte : -(P i).residual x / dot (P i).a p=t := by
      apply (div_eq_iff hp).mpr
      rw [hz] at he
      linarith
    exact hn (Set.mem_range.mpr ⟨i,hte⟩)
  exact ht.2 (DifferentiableAt.sum (fun i _ => hc i))


def objective {n : ℕ} {ι : Type*} [Fintype ι] (ψ : Vec n → ℝ) (P : ι → Kink n)
    (x : Vec n) : ℝ := ψ x+penalty P x

theorem objective_convex {n : ℕ} {ι : Type*} [Fintype ι] {ψ : Vec n → ℝ}
    (hψ : ConvexOn ℝ univ ψ) (P : ι → Kink n) : ConvexOn ℝ univ (objective ψ P) :=
  hψ.add (penalty_convex P)

theorem objective_finite_bad_ray {n : ℕ} {ι : Type*} [Fintype ι] {ψ : Vec n → ℝ}
    (hψ : Differentiable ℝ ψ) (P : ι → Kink n) {x : Vec n}
    (hd : DifferentiableAt ℝ (objective ψ P) x) (p : Vec n) :
    {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ (objective ψ P) (x+t • p)}.Finite := by
  have hp : DifferentiableAt ℝ (penalty P) x := by
    simpa [objective] using hd.sub (hψ x)
  apply (penalty_finite_bad_ray P hp p).subset
  intro t ht
  refine ⟨ht.1,?_⟩
  intro hc
  exact ht.2 ((hψ (x+t • p)).add hc)

/-- Source F's existence theorem for the literal finite affine-kink class.
All finite full-space bad-ray data are derived; no nondegenerate-ray premise is added. -/
theorem fullBFGS_step_exists {n : ℕ} {ι : Type*} [Fintype ι] {ψ : Vec n → ℝ}
    (hψ : Differentiable ℝ ψ) (P : ι → Kink n)
    (hF : ConvexOn ℝ univ (objective ψ P)) (x g : Vec n) (H : Mat n)
    (hH : H.PosDef) (hgn : g ≠ 0) (hg : HasFDerivAt (objective ψ P) (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ objective ψ P (x+bfgsStep H g t)) :
    ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt (objective ψ P) (gradientFunctional h) (x+bfgsStep H g α) ∧
      objective ψ P (x+bfgsStep H g α) < objective ψ P x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  apply FiniteRayLineSearch.fullBFGS_step_exists hF x g H hH hgn hg hc₁ hc hc₂ L hL
  have hb := objective_finite_bad_ray hψ P hg.differentiableAt (bfgsStep H g 1)
  simpa only [← FiniteRayLineSearch.bfgsStep_scaling] using hb

namespace Kink

def absolute {n : ℕ} (a : Vec n) (b : ℝ) : Kink n := ⟨a,b,-1,1,by norm_num⟩
def hinge {n : ℕ} (a : Vec n) (b : ℝ) : Kink n := ⟨a,b,0,1,by norm_num⟩
def quantile {n : ℕ} (a : Vec n) (b τ : ℝ) : Kink n := ⟨a,b,τ-1,τ,by linarith⟩

theorem absolute_value {n : ℕ} (a : Vec n) (b : ℝ) (x : Vec n) :
    (absolute a b).value x=|dot a x-b| := by
  simp only [absolute,value,residual,neg_one_mul,one_mul]
  rw [max_comm,← abs_eq_max_neg]

theorem hinge_value {n : ℕ} (a : Vec n) (b : ℝ) (x : Vec n) :
    (hinge a b).value x=max 0 (dot a x-b) := by simp [hinge,value,residual]

theorem quantile_value {n : ℕ} (a : Vec n) (b τ : ℝ) (x : Vec n) :
    (quantile a b τ).value x=τ*max (dot a x-b) 0+(1-τ)*max (-(dot a x-b)) 0 := by
  let r := dot a x-b
  change max ((τ-1)*r) (τ*r)=τ*max r 0+(1-τ)*max (-r) 0
  rcases le_total 0 r with hr | hr
  · rw [max_eq_right (by nlinarith),max_eq_left hr,max_eq_right (neg_nonpos.mpr hr)]
    ring
  · rw [max_eq_left (by nlinarith),max_eq_right hr,max_eq_left (neg_nonneg.mpr hr)]
    ring

end Kink

end BfgsVerification.AffineKinks


