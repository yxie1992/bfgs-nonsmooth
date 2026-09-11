import BfgsVerification.SimpleRootBox
import BfgsVerification.SemialgebraicRootBoxes

/-! A genuine nonlinear parameter-uniform local projection theorem. An actual
simple root of an arbitrary polynomial yields a smooth semialgebraic root graph
on fixed coordinate neighborhoods. Singular/global cases remain separate. -/
noncomputable section
open scoped Topology ContDiff
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- Actual polynomial inputs alone produce a local smooth semialgebraic root
selector, with uniform uniqueness on a fixed scalar interval. -/
theorem polynomial_simple_root_chart {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (b : ℝ)
    (hzero : (fiberPolynomial p a).eval b = 0)
    (hsimple : (fiberPolynomial p a).derivative.eval b ≠ 0) :
    ∃ g : Vec n → ℝ, ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ g a = b ∧
      ContDiffOn ℝ ∞ g (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, dist (g x) b < δ ∧
        ∀ t : ℝ, dist t b < δ → (parameterEval p (x,t) = 0 ↔ t = g x)) ∧
      IsSemialgebraic {v : Option (Fin n) → ℝ |
        (fun i => v (some i)) ∈ Metric.ball a r ∧ v none = g (fun i => v (some i))} := by
  have h0 : parameterEval p (a,b) = 0 := by rwa [← fiberPolynomial_eval]
  have hd : fderiv ℝ (parameterEval p) (a,b) (0,1) ≠ 0 := by
    rwa [parameterEval_vertical_derivative]
  obtain ⟨g,r,δ,hr,hδ,hga,hgc,hroots⟩ := exists_smooth_root_box
    (analytic_parameterEval p (a,b)).contDiffAt h0 hd
  exact ⟨g,r,δ,hr,hδ,hga,hgc,hroots,local_root_graph_semialgebraic p a b hr g hroots⟩

theorem isSemialgebraic_pi_ball {n : ℕ} (a : Vec n) {r : ℝ} (hr : 0 < r) :
    IsSemialgebraic (Metric.ball a r) := by
  have h := isSemialgebraic_finset_inter Finset.univ
    (fun i : Fin n => {v : Vec n | dist (v i) (a i) < r})
    (fun i _ => isSemialgebraic_coordinate_band i (a i) r)
  convert h using 1
  ext v
  simp only [Metric.mem_ball,dist_pi_lt_iff hr,mem_iInter,mem_setOf_eq,Finset.mem_univ,forall_const]

/-- Around an actual simple root, existential projection of the actual
polynomial zero set restricted to fixed boxes is exactly the parameter ball,
and hence is semialgebraic. No nonlinear projection closure is assumed. -/
theorem polynomial_simple_root_local_projection {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (b : ℝ)
    (hzero : (fiberPolynomial p a).eval b = 0)
    (hsimple : (fiberPolynomial p a).derivative.eval b ≠ 0) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      {x : Vec n | x ∈ Metric.ball a r ∧ ∃ t : ℝ, dist t b < δ ∧ parameterEval p (x,t) = 0} =
        Metric.ball a r ∧
      IsSemialgebraic {x : Vec n | x ∈ Metric.ball a r ∧
        ∃ t : ℝ, dist t b < δ ∧ parameterEval p (x,t) = 0} := by
  obtain ⟨g,r,δ,hr,hδ,hga,hgc,hroots,hgraph⟩ := polynomial_simple_root_chart p a b hzero hsimple
  have he : {x : Vec n | x ∈ Metric.ball a r ∧
      ∃ t : ℝ, dist t b < δ ∧ parameterEval p (x,t) = 0} = Metric.ball a r := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      have hg := hroots x hx
      exact ⟨hx,g x,hg.1,(hg.2 _ hg.1).mpr rfl⟩
  exact ⟨r,δ,hr,hδ,he,he.symm ▸ isSemialgebraic_pi_ball a hr⟩

end RealAlgebraicGeometry
end BfgsVerification
