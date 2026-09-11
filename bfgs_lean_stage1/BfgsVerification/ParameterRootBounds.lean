import BfgsVerification.PolynomialFiberDegree
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.Lattice

noncomputable section
open Filter Set Polynomial
open scoped Topology NNReal
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

/-- A coefficient formula for the Cauchy bound on a leading-coefficient chart. -/
def parameterCauchyBound (p : Polynomial (MvPolynomial (Fin n) ℝ)) (x : Vec n) : ℝ≥0 :=
  (Finset.range p.natDegree).sup (fun i => ‖MvPolynomial.eval x (p.coeff i)‖₊) /
    ‖MvPolynomial.eval x p.leadingCoeff‖₊ + 1

theorem parameterCauchyBound_specialize (p : Polynomial (MvPolynomial (Fin n) ℝ))
    (x : Vec n) (hx : MvPolynomial.eval x p.leadingCoeff ≠ 0) :
    (p.map (MvPolynomial.eval x)).cauchyBound = parameterCauchyBound p x := by
  unfold Polynomial.cauchyBound parameterCauchyBound
  rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hx,
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hx]
  simp only [Polynomial.coeff_map]

theorem parameterCauchyBound_continuousAt (p : Polynomial (MvPolynomial (Fin n) ℝ))
    {a : Vec n} (ha : MvPolynomial.eval a p.leadingCoeff ≠ 0) :
    ContinuousAt (parameterCauchyBound p) a := by
  have hs : Continuous (fun x : Vec n =>
      (Finset.range p.natDegree).sup (fun i => ‖MvPolynomial.eval x (p.coeff i)‖₊)) :=
    Continuous.finset_sup_apply (fun i _ => (MvPolynomial.continuous_eval (p.coeff i)).nnnorm)
  have hl : Continuous (fun x : Vec n => ‖MvPolynomial.eval x p.leadingCoeff‖₊) :=
    (MvPolynomial.continuous_eval p.leadingCoeff).nnnorm
  exact (hs.continuousAt.div hl.continuousAt (by simpa using ha)).add continuousAt_const

theorem parameter_roots_eventually_bounded (p : Polynomial (MvPolynomial (Fin n) ℝ))
    {a : Vec n} (ha : MvPolynomial.eval a p.leadingCoeff ≠ 0) :
    ∃ R : ℝ, 0<R ∧ ∀ᶠ x in 𝓝 a, ∀ t : ℝ,
      (p.map (MvPolynomial.eval x)).IsRoot t → |t|<R := by
  let R : ℝ≥0 := parameterCauchyBound p a+1
  refine ⟨R, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ≥0)<R from by dsimp [R]; positivity)
  have hb : ∀ᶠ x in 𝓝 a, parameterCauchyBound p x<R :=
    (parameterCauchyBound_continuousAt p ha).eventually
      (gt_mem_nhds (show parameterCauchyBound p a<R from by dsimp [R]; exact lt_add_one _))
  have hl : ∀ᶠ x in 𝓝 a, MvPolynomial.eval x p.leadingCoeff ≠ 0 :=
    (MvPolynomial.continuous_eval p.leadingCoeff).continuousAt.eventually_ne ha
  filter_upwards [hb, hl] with x hbx hlx
  have hp : p.map (MvPolynomial.eval x) ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rwa [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlx]
  intro t ht
  have hroot := ht.norm_lt_cauchyBound hp
  rw [parameterCauchyBound_specialize p x hlx] at hroot
  have hh : ‖t‖₊<R := hroot.trans hbx
  exact_mod_cast hh

end RealAlgebraicGeometry
end BfgsVerification
