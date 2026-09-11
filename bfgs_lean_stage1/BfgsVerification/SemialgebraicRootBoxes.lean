import BfgsVerification.PolynomialFibers

/-! Actual semialgebraic coordinate boxes and local root graphs. The graph
identity uses the proved fixed-interval root characterization, not a projection
closure premise. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem isSemialgebraic_coordinate_band {σ : Type*} [Finite σ] (i : σ) (b δ : ℝ) :
    IsSemialgebraic {v : σ → ℝ | dist (v i) b < δ} := by
  have h := (isSemialgebraic_positive (X i - C (b-δ) : MvPolynomial σ ℝ)).inter
    (isSemialgebraic_positive (C (b+δ) - X i : MvPolynomial σ ℝ))
  convert h using 1
  ext v
  simp only [mem_setOf_eq,mem_inter_iff,MvPolynomial.eval_sub,MvPolynomial.eval_X,
    MvPolynomial.eval_C,Real.dist_eq,abs_lt]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem isSemialgebraic_parameter_ball {n : ℕ} (a : Vec n) {r : ℝ} (hr : 0 < r) :
    IsSemialgebraic {v : Option (Fin n) → ℝ | (fun i => v (some i)) ∈ Metric.ball a r} := by
  have h := isSemialgebraic_finset_inter Finset.univ
    (fun i : Fin n => {v : Option (Fin n) → ℝ | dist (v (some i)) (a i) < r})
    (fun i _ => isSemialgebraic_coordinate_band (some i) (a i) r)
  convert h using 1
  ext v
  simp only [mem_setOf_eq,Metric.mem_ball,dist_pi_lt_iff hr,mem_iInter,Finset.mem_univ,forall_const]

/-- Once the local root is uniquely identified on a product box, its actual
graph is the polynomial zero set intersected with explicit coordinate bands. -/
theorem local_root_graph_semialgebraic {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (b : ℝ)
    {r δ : ℝ} (hr : 0 < r) (g : Vec n → ℝ)
    (hroot : ∀ x ∈ Metric.ball a r, dist (g x) b < δ ∧
      ∀ t : ℝ, dist t b < δ → (parameterEval p (x,t) = 0 ↔ t = g x)) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ Metric.ball a r ∧ v none = g (fun i => v (some i))} := by
  have h := (isSemialgebraic_parameter_ball a hr).inter
    ((isSemialgebraic_coordinate_band none b δ).inter (isSemialgebraic_equal_zero p))
  convert h using 1
  ext v
  simp only [mem_setOf_eq,mem_inter_iff]
  have hp : parameterEval p ((fun i => v (some i)),v none) = MvPolynomial.eval v p := by
    apply congrArg (fun q : Option (Fin n) → ℝ => MvPolynomial.eval q p)
    funext i
    cases i <;> rfl
  constructor
  · rintro ⟨hv,he⟩
    have hg := hroot _ hv
    have hdist : dist (v none) b < δ := by rw [he]; exact hg.1
    refine ⟨hv,hdist,?_⟩
    rw [← hp]
    exact (hg.2 _ hdist).mpr he
  · rintro ⟨hv,hdist,hp0⟩
    refine ⟨hv,?_⟩
    apply ((hroot _ hv).2 _ hdist).mp
    rwa [hp]

end RealAlgebraicGeometry
end BfgsVerification
