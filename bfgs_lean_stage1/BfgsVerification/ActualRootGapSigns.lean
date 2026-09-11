import BfgsVerification.PolynomialZeroPatterns
import BfgsVerification.CylinderCoordinateCovers
import BfgsVerification.OrderedRootBranches

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n m : ℕ}

theorem actual_ordered_gap_eval_ne_zero
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (S : Set (Vec n))
    (hS : S ⊆ rootSignatureStratum (MvPolynomial.optionEquivLeft ℝ (Fin n) p) a)
    (hp : ∀ x ∈ S, fiberPolynomial p x ≠ 0)
    (j : Fin ((fiberPolynomial p a).roots.toFinset.card+1))
    {z : Vec n × ℝ}
    (hz : z ∈ orderedGapCell S
      (fun i : Fin (fiberPolynomial p a).roots.toFinset.card => orderedFiberRoot p i.val) j) :
    (fiberPolynomial p z.1).eval z.2 ≠ 0 := by
  intro he
  obtain ⟨k,hk,hkt⟩ := (isRoot_iff_exists_orderedRealRoot _ (hp z.1 hz.1) z.2).mp he
  have hcard : (fiberPolynomial p z.1).roots.toFinset.card = (fiberPolynomial p a).roots.toFinset.card := by
    simpa only [← fiberPolynomial_eq_map] using (hS hz.1).2.1
  let i : Fin (fiberPolynomial p a).roots.toFinset.card := ⟨k,hcard ▸ hk⟩
  have hfi : orderedFiberRoot p i.val z.1 = z.2 := hkt
  by_cases hij : i.val < j.val
  · have h := hz.2.1 i hij
    dsimp only at h
    rw [hfi] at h
    exact lt_irrefl _ h
  · have h := hz.2.2 i (Nat.le_of_not_gt hij)
    dsimp only at h
    rw [hfi] at h
    exact lt_irrefl _ h

theorem actual_ordered_root_family_strictMono
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (S : Set (Vec n))
    (hS : S ⊆ rootSignatureStratum (MvPolynomial.optionEquivLeft ℝ (Fin n) p) a) :
    ∀ x ∈ S, StrictMono (fun i : Fin (fiberPolynomial p a).roots.toFinset.card =>
      orderedFiberRoot p i.val x) := by
  intro x hx i j hij
  apply orderedRealRoot_lt _ hij
  have hcard : (fiberPolynomial p x).roots.toFinset.card = (fiberPolynomial p a).roots.toFinset.card := by
    simpa only [← fiberPolynomial_eq_map] using (hS hx).2.1
  change j.val < (fiberPolynomial p x).roots.toFinset.card
  rw [hcard]
  exact j.isLt

theorem actual_ordered_root_family_smooth
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n) (S : Set (Vec n))
    (hS : S ⊆ rootSignatureStratum (MvPolynomial.optionEquivLeft ℝ (Fin n) p) a) :
    ∀ i : Fin (fiberPolynomial p a).roots.toFinset.card,
      ContDiffOn ℝ ∞ (orderedFiberRoot p i.val) S :=
  fun i => (orderedFiberRoot_contDiffOn_signature p a i.isLt).mono hS

/-- Every input factor has constant actual sign on each connected gap over a
fixed zero-factor pattern and actual surviving-product signature. -/
theorem input_sign_constant_on_actual_gap
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ) (Z : Finset (Fin m))
    (a : Vec n) (S : Set (Vec n)) (hpath : PiecewiseSmoothConnected S)
    (hzero : S ⊆ zeroFiberPattern P Z)
    (hS : S ⊆ rootSignatureStratum
      (MvPolynomial.optionEquivLeft ℝ (Fin n) (survivingPolynomialProduct P Z)) a)
    (j : Fin ((fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card+1))
    (i : Fin m) {x y : Vec n × ℝ}
    (hx : x ∈ orderedGapCell S
      (fun k : Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card =>
        orderedFiberRoot (survivingPolynomialProduct P Z) k.val) j)
    (hy : y ∈ orderedGapCell S
      (fun k : Fin (fiberPolynomial (survivingPolynomialProduct P Z) a).roots.toFinset.card =>
        orderedFiberRoot (survivingPolynomialProduct P Z) k.val) j) :
    SignType.sign (parameterEval (P i) x) = SignType.sign (parameterEval (P i) y) := by
  by_cases hi : i ∈ Z
  · have hx0 := zero_pattern_factor_eval_zero P Z (hzero hx.1) x.2 i hi
    have hy0 := zero_pattern_factor_eval_zero P Z (hzero hy.1) y.2 i hi
    simpa only [fiberPolynomial_eval] using congrArg SignType.sign (hx0.trans hy0.symm)
  · let p := survivingPolynomialProduct P Z
    have hg := orderedGapCell_piecewiseSmoothConnected S
      (fun k : Fin (fiberPolynomial p a).roots.toFinset.card => orderedFiberRoot p k.val)
      hpath (actual_ordered_root_family_smooth p a S hS)
      (actual_ordered_root_family_strictMono p a S hS) j
    apply sign_constant_on_preconnected hg.isPreconnected
      (fun z _ => (analytic_parameterEval (P i) z).continuousAt.continuousWithinAt) ?_ hx hy
    intro z hz
    have hpz : (fiberPolynomial p z.1).eval z.2 ≠ 0 :=
      actual_ordered_gap_eval_ne_zero p a S hS
        (fun x hx => survivingProduct_fiber_nonzero P Z (hzero hx)) j hz
    simpa only [fiberPolynomial_eval] using factor_nonzero_off_surviving_root P Z z.1 z.2 i hi hpz

end RealAlgebraicGeometry
end BfgsVerification
