import BfgsVerification.SemialgebraicMapGraphs
import BfgsVerification.PiecewiseSmoothConcatenation

noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- Semialgebraicity of the actual graph on the path's parameter domain.
No condition is imposed on the arbitrary extension outside that domain. -/
def IsSemialgebraicCurveOn (p : ℝ → σ → ℝ) (J : Set ℝ) : Prop :=
  IsSemialgebraic {v : Option σ → ℝ |
    v none ∈ J ∧ (fun i => v (some i)) = p (v none)}

theorem semialgebraic_curve_interval (a b : ℝ) :
    IsSemialgebraic {v : Option σ → ℝ | v none ∈ Icc a b} := by
  have hl := isSemialgebraic_nonnegative (X none - C a : MvPolynomial (Option σ) ℝ)
  have hu := isSemialgebraic_nonnegative (C b - X none : MvPolynomial (Option σ) ℝ)
  convert hl.inter hu using 1
  ext v
  simp only [mem_setOf_eq,mem_inter_iff,mem_Icc,MvPolynomial.eval_sub,
    MvPolynomial.eval_X,MvPolynomial.eval_C,sub_nonneg]

theorem IsSemialgebraicCurveOn.affine (a b : σ → ℝ) :
    IsSemialgebraicCurveOn (fun t i => a i * t + b i) (Icc 0 1) := by
  have heq := isSemialgebraic_forall_finite
    (fun i : σ => {v : Option σ → ℝ | v (some i) = a i * v none + b i})
    (fun i => by
      convert isSemialgebraic_equal_zero
        (X (some i) - (C (a i) * X none + C (b i)) : MvPolynomial (Option σ) ℝ) using 1
      ext v
      simp only [mem_setOf_eq,MvPolynomial.eval_sub,MvPolynomial.eval_add,MvPolynomial.eval_mul,
        MvPolynomial.eval_X,MvPolynomial.eval_C,sub_eq_zero])
  unfold IsSemialgebraicCurveOn
  convert (semialgebraic_curve_interval (σ := σ) 0 1).inter heq using 1
  ext v
  simp only [mem_inter_iff,mem_setOf_eq,_root_.funext_iff]

theorem IsSemialgebraicCurveOn.const (x : σ → ℝ) :
    IsSemialgebraicCurveOn (fun _ => x) (Icc 0 1) := by
  simpa only [Pi.zero_apply,zero_mul,zero_add] using IsSemialgebraicCurveOn.affine (0 : σ → ℝ) x

theorem IsSemialgebraicCurveOn.segment (x y : σ → ℝ) :
    IsSemialgebraicCurveOn (fun t => (1-t) • x + t • y) (Icc 0 1) := by
  have he : (fun t => (1-t) • x + t • y) = (fun t i => (y i-x i)*t+x i) := by
    funext t i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact IsSemialgebraicCurveOn.affine (y-x) x

theorem IsSemialgebraicCurveOn.map {p : ℝ → σ → ℝ} {J : Set ℝ}
    (hp : IsSemialgebraicCurveOn p J) {G : (σ → ℝ) → τ → ℝ}
    {S : Set (σ → ℝ)} (hG : IsSemialgebraicMapOn G S) (hpS : MapsTo p J S) :
    IsSemialgebraicCurveOn (G ∘ p) J := by
  let a : Option σ → Option τ ⊕ σ := fun j => Option.elim j (.inl none) Sum.inr
  let b : σ ⊕ τ → Option τ ⊕ σ := Sum.elim Sum.inr (fun j => .inl (some j))
  have h := coordinate_projection_semialgebraic ((hp.reindex a).inter (hG.reindex b))
  unfold IsSemialgebraicCurveOn
  convert h using 1
  ext v
  change (_ ∈ J ∧ _ = _) ↔ ∃ x : σ → ℝ, _
  simp only [mem_inter_iff,mem_setOf_eq,a,b,Option.elim_none,Option.elim_some,
    Sum.elim_inl,Sum.elim_inr]
  constructor
  · rintro ⟨ht,hv⟩
    exact ⟨p (v none),⟨ht,rfl⟩,hpS ht,hv⟩
  · rintro ⟨x,⟨ht,hx⟩,_,hv⟩
    change x = _ at hx
    subst x
    exact ⟨ht,hv⟩

theorem IsSemialgebraicCurveOn.affine_precomp {p : ℝ → σ → ℝ}
    (hp : IsSemialgebraicCurveOn p (Icc 0 1)) (a b : ℝ)
    (hm : MapsTo (fun t => a*t+b) (Icc 0 1) (Icc 0 1)) :
    IsSemialgebraicCurveOn (fun t => p (a*t+b)) (Icc 0 1) := by
  let P : Option σ → MvPolynomial (Option σ) ℝ :=
    fun i => Option.elim i (C a * X none + C b) (fun j => X (some j))
  have h := (semialgebraic_curve_interval (σ := σ) 0 1).inter (hp.polynomial_preimage P)
  unfold IsSemialgebraicCurveOn
  convert h using 1
  ext v
  simp only [mem_inter_iff,mem_preimage,mem_setOf_eq,P,Option.elim_none,Option.elim_some,
    MvPolynomial.eval_add,MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  exact ⟨fun h => ⟨h.1,hm h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

theorem IsSemialgebraicCurveOn.symm {p : ℝ → σ → ℝ}
    (hp : IsSemialgebraicCurveOn p (Icc 0 1)) :
    IsSemialgebraicCurveOn (fun t => p (1-t)) (Icc 0 1) := by
  have hm : MapsTo (fun t : ℝ => (-1)*t+1) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    change 0 ≤ (-1)*t+1 ∧ (-1)*t+1 ≤ 1
    exact ⟨by linarith [ht.2],by linarith [ht.1]⟩
  simpa only [neg_one_mul,neg_add_eq_sub] using hp.affine_precomp (-1) 1 hm

end RealAlgebraicGeometry
end BfgsVerification
