import BfgsVerification.EuclideanResidualRadial
import BfgsVerification.AffineKinkAlgebra

noncomputable section
open scoped BigOperators Topology RealInnerProductSpace
open Set Filter
namespace BfgsVerification.EuclideanResidual

theorem norm_residual_convex {n m : ℕ} (A : Vec n →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) : ConvexOn ℝ univ (fun x => ‖residual A b x‖) := by
  refine ⟨convex_univ,?_⟩
  intro x _ z _ α β hα hβ hab
  have he : residual A b (α • x+β • z)=α • residual A b x+β • residual A b z := by
    simp only [residual,map_add,map_smul,smul_sub]
    have hb : α • b+β • b=b := by rw [← add_smul,hab,one_smul]
    calc
      α • A x+β • A z-b = α • A x+β • A z-(α • b+β • b) := by rw [hb]
      _ = _ := by abel
  change ‖residual A b (α • x+β • z)‖ ≤ α*‖residual A b x‖+β*‖residual A b z‖
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul,norm_smul,Real.norm_of_nonneg hα,Real.norm_of_nonneg hβ])

def normSupportVector {n m : ℕ} (A : Vec n →L[ℝ] EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) : Vec n := fun i => ⟪u, A (Pi.single i 1)⟫

theorem normSupportVector_dot {n m : ℕ} (A : Vec n →L[ℝ] EuclideanSpace ℝ (Fin m))
    (u : EuclideanSpace ℝ (Fin m)) (v : Vec n) :
    dot (normSupportVector A u) v=⟪u, A v⟫ := by
  have he := gradientFunctional_coordinates ((innerSL ℝ u).comp A)
  have hh := congrArg (fun l : Vec n →L[ℝ] ℝ => l v) he
  simpa only [gradientFunctional_apply,ContinuousLinearMap.comp_apply,innerSL_apply,normSupportVector] using hh

theorem norm_support_at_zero {n m : ℕ} (A : Vec n →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b u : EuclideanSpace ℝ (Fin m)) {x : Vec n} (hx : residual A b x=0) (hu : ‖u‖ ≤ 1) :
    Homogeneous.Supports (fun z => ‖residual A b z‖) x (normSupportVector A u) := by
  intro z
  change dot (normSupportVector A u) (z-x) ≤ ‖residual A b z‖-‖residual A b x‖
  rw [hx,norm_zero,sub_zero,normSupportVector_dot]
  have he : A (z-x)=residual A b z := by rw [map_sub,sub_eq_zero.mp hx]; rfl
  rw [he]
  exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (residual A b z)])

def normPenalty {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) (x : Vec n) : ℝ :=
  ∑ i, ‖residual (A i) (b i) x‖

/-- Initial full-sum differentiability rules out a zero residual for every
nonconstant Euclidean residual term. -/
theorem initial_norm_residual_ne_zero {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) {x : Vec n}
    (hd : DifferentiableAt ℝ (normPenalty A b) x) (i : ι) (ha : A i ≠ 0) :
    residual (A i) (b i) x ≠ 0 := by
  intro hx
  have hv : ∃ v, A i v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact ha (ContinuousLinearMap.ext hn)
  obtain ⟨v,hv⟩ := hv
  let u := ‖A i v‖⁻¹ • A i v
  have hnorm : ‖A i v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖u‖ ≤ 1 := by
    dsimp [u]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hnorm]
  have he := AffineKinks.sum_component_supports_equal
    (fun j => norm_residual_convex (A j) (b j)) hd i
    (norm_support_at_zero (A i) (b i) u hx hu)
    (norm_support_at_zero (A i) (b i) 0 hx (by simp))
  have hp := congrArg (fun g => dot g v) he
  dsimp only [] at hp
  rw [normSupportVector_dot,normSupportVector_dot,inner_zero_left] at hp
  change ⟪‖A i v‖⁻¹ • A i v,A i v⟫=0 at hp
  rw [real_inner_smul_left,real_inner_self_eq_norm_sq] at hp
  have hz : ‖A i v‖=0 := by field_simp [hnorm] at hp
  exact hnorm hz

theorem norm_residual_on_ray {n m : ℕ} (A : Vec n →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (x p : Vec n) (t : ℝ) :
    residual A b (x+t • p)=residual A b x+t • A p := by
  simp only [residual,map_add,map_smul]
  abel

theorem normPenalty_finite_bad_ray {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i))) {x : Vec n}
    (hd : DifferentiableAt ℝ (normPenalty A b) x) (p : Vec n) :
    {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ (normPenalty A b) (x+t • p)}.Finite := by
  classical
  let time (i : ι) : ℝ := -⟪A i p,residual (A i) (b i) x⟫ / ‖A i p‖^2
  apply (Set.finite_range time).subset
  intro t ht
  by_contra hn
  have hdif (i : ι) : DifferentiableAt ℝ (fun z => ‖residual (A i) (b i) z‖) (x+t • p) := by
    by_cases ha : A i=0
    · simpa only [ha,residual,ContinuousLinearMap.zero_apply,zero_sub,norm_neg] using
        (differentiableAt_const ‖b i‖ : DifferentiableAt ℝ (fun _ : Vec n => ‖b i‖) _)
    have hr : residual (A i) (b i) (x+t • p) ≠ 0 := by
      intro hz
      have hstart := initial_norm_residual_ne_zero A b hd i ha
      have he := norm_residual_on_ray (A i) (b i) x p t
      have hp : A i p ≠ 0 := by
        intro hp
        rw [hp,smul_zero,add_zero,hz] at he
        exact hstart he.symm
      have hnorm : ‖A i p‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hp)
      have heq : time i=t := by
        have hi := congrArg (fun w => ⟪A i p,w⟫) he
        dsimp only [] at hi
        rw [hz,inner_zero_right,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at hi
        apply (div_eq_iff hnorm).mpr
        linarith
      exact hn (Set.mem_range.mpr ⟨i,heq⟩)
    exact ((residual_contDiff (N := 1) (A i) (b i)).differentiable (by norm_num) _).norm ℝ hr
  exact ht.2 (DifferentiableAt.sum (fun i _ => hdif i))

/-- Actual full-space bad times for a smooth loss plus a finite Euclidean
residual sum; no nonzero or generic-ray assumption is imposed on the data. -/
theorem norm_objective_finite_bad_ray {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hψ : Differentiable ℝ ψ)
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i)))
    (hrep : ∀ z, F z=ψ z+normPenalty A b z) {x : Vec n}
    (hd : DifferentiableAt ℝ F x) (p : Vec n) :
    {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ F (x+t • p)}.Finite := by
  have he : F=fun z => ψ z+normPenalty A b z := funext hrep
  subst F
  have hp : DifferentiableAt ℝ (normPenalty A b) x := by
    simpa using hd.sub (hψ x)
  apply (normPenalty_finite_bad_ray A b hp p).subset
  intro t ht
  refine ⟨ht.1,?_⟩
  intro hc
  exact ht.2 ((hψ (x+t • p)).add hc)

/-- Literal Euclidean residual source family: an actual differentiable strict
Armijo–weak-Wolfe point exists for every SPD descent metric and bounded-below ray. -/
theorem euclidean_residual_fullBFGS_step_exists {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hψ : Differentiable ℝ ψ)
    (A : ∀ i, Vec n →L[ℝ] EuclideanSpace ℝ (Fin (m i)))
    (b : ∀ i, EuclideanSpace ℝ (Fin (m i)))
    (hrep : ∀ z, F z=ψ z+∑ i, ‖residual (A i) (b i) z‖) (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hgn : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+bfgsStep H g t)) :
    ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt F (gradientFunctional h) (x+bfgsStep H g α) ∧
      F (x+bfgsStep H g α) < F x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  apply FiniteRayLineSearch.fullBFGS_step_exists hF x g H hH hgn hg hc₁ hc hc₂ L hL
  have hb := norm_objective_finite_bad_ray hψ A b hrep hg.differentiableAt (bfgsStep H g 1)
  simpa only [← FiniteRayLineSearch.bfgsStep_scaling] using hb

theorem matrix_euclidean_residual_fullBFGS_step_exists {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F ψ : Vec n → ℝ} (hψ : Differentiable ℝ ψ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin n) ℝ) (b : ∀ i, Vec (m i))
    (hrep : ∀ z, F z=ψ z+∑ i, ‖euclideanVector ((A i).mulVec z-b i)‖)
    (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hgn : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+bfgsStep H g t)) :
    ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt F (gradientFunctional h) (x+bfgsStep H g α) ∧
      F (x+bfgsStep H g α) < F x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  apply euclidean_residual_fullBFGS_step_exists hψ (fun i => matrixEuclideanCLM (A i))
    (fun i => euclideanVector (b i)) _ hF x g H hH hgn hg hc₁ hc hc₂ L hL
  simpa only [matrix_residual] using hrep

end BfgsVerification.EuclideanResidual
