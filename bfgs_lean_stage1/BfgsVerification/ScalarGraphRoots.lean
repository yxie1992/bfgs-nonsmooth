import BfgsVerification.ScalarSemialgebraicBoundary

noncomputable section
open Set Filter Polynomial
open scoped Topology ContDiff
namespace BfgsVerification.RealAlgebraicGeometry

/-- Every isolated point of an actual Boolean-polynomial fiber is a root of
an atom whose entire fiber is nonzero. Zero fibers contribute no boundaries. -/
theorem isolated_formula_fiber_has_nonzero_atom_root {n m : ℕ}
    (f : PolynomialFormula (Option (Fin n)))
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ i, P i = p)
    (x : Vec n) (t : ℝ) (ht : f.Holds (parameterPoint x t))
    (hunique : ∀ u, f.Holds (parameterPoint x u) → u = t) :
    ∃ i, fiberPolynomial (P i) x ≠ 0 ∧ (fiberPolynomial (P i) x).IsRoot t := by
  classical
  by_contra hn
  have heach : ∀ i, ∀ᶠ u in 𝓝 t,
      SignType.sign ((fiberPolynomial (P i) x).eval u) =
        SignType.sign ((fiberPolynomial (P i) x).eval t) := by
    intro i
    by_cases hp : fiberPolynomial (P i) x = 0
    · simp only [hp,Polynomial.eval_zero]
      exact Filter.Eventually.of_forall (fun _ => True.intro)
    · have hz : (fiberPolynomial (P i) x).eval t ≠ 0 :=
        fun he => hn ⟨i,hp,he⟩
      have hsign : ContinuousAt (SignType.sign : ℝ → SignType) ((fiberPolynomial (P i) x).eval t) :=
        continuousAt_sign_of_ne_zero hz
      have hpoly : ContinuousAt (fun u : ℝ => (fiberPolynomial (P i) x).eval u) t :=
        (fiberPolynomial (P i) x).continuous.continuousAt
      have hc := hsign.comp (f := fun u : ℝ => (fiberPolynomial (P i) x).eval u) hpoly
      exact hc.eventually (isOpen_discrete ({SignType.sign ((fiberPolynomial (P i) x).eval t)} : Set SignType)
        |>.mem_nhds (mem_singleton _))
  have hall : ∀ᶠ u in 𝓝 t, ∀ i, SignType.sign ((fiberPolynomial (P i) x).eval u) =
      SignType.sign ((fiberPolynomial (P i) x).eval t) := Filter.eventually_all.mpr heach
  have heq : ∀ᶠ u in 𝓝 t, u = t := by
    filter_upwards [hall] with u hu
    apply hunique u
    have hs : ∀ p ∈ f.atomPolynomials,
        SignType.sign (MvPolynomial.eval (parameterPoint x u) p) =
          SignType.sign (MvPolynomial.eval (parameterPoint x t) p) := by
      intro p hp
      obtain ⟨i,rfl⟩ := hP p hp
      simpa only [fiberPolynomial_eval,parameterEval] using hu i
    rw [f.holds_iff_signHolds] at ht ⊢
    exact (f.signHolds_congr hs).mpr ht
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp heq
  have hbad := hball (show t + ε / 2 ∈ Metric.ball t ε by
    rw [Metric.mem_ball,Real.dist_eq]
    have he : t + ε / 2 - t = ε / 2 := by ring
    rw [he,abs_of_pos (by positivity)]
    linarith)
  change t + ε / 2 = t at hbad
  linarith

theorem singleton_formula_fiber_is_surviving_root {n m : ℕ}
    (f : PolynomialFormula (Option (Fin n)))
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (hP : ∀ p ∈ f.atomPolynomials, ∃ i, P i = p)
    (Z : Finset (Fin m)) (x : Vec n) (hx : x ∈ zeroFiberPattern P Z)
    (t : ℝ) (ht : f.Holds (parameterPoint x t))
    (hunique : ∀ u, f.Holds (parameterPoint x u) → u = t) :
    (fiberPolynomial (survivingPolynomialProduct P Z) x).IsRoot t := by
  obtain ⟨i,hi,hroot⟩ := isolated_formula_fiber_has_nonzero_atom_root f P hP x t ht hunique
  exact survivingProduct_eval_zero_of_factor P Z x t i (fun h => hi ((hx i).mp h)) hroot

end BfgsVerification.RealAlgebraicGeometry
