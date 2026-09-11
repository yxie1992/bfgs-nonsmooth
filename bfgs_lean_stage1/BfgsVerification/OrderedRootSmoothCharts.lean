import BfgsVerification.ParameterOrderedRootContinuity
import BfgsVerification.MultiplicityRootCharts

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

def orderedFiberRoot (p : MvPolynomial (Option (Fin n)) ℝ) (k : ℕ) (x : Vec n) : ℝ :=
  orderedRealRoot (fiberPolynomial p x) k

/-- Ordered root branches on an actual root-signature stratum are locally
restrictions of smooth ambient functions, even at multiple roots and on
lower-dimensional parameter strata. -/
theorem orderedFiberRoot_local_smooth_extension
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n)
    (hp : fiberPolynomial p a ≠ 0) {k : ℕ}
    (hk : k < (fiberPolynomial p a).roots.toFinset.card) {S : Set (Vec n)}
    (hS : S ⊆ rootSignatureStratum (MvPolynomial.optionEquivLeft ℝ (Fin n) p) a) :
    ∃ g : Vec n → ℝ, ContDiffAt ℝ ∞ g a ∧ g a = orderedFiberRoot p k a ∧
      orderedFiberRoot p k =ᶠ[𝓝[S] a] g := by
  let q := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  let b := orderedFiberRoot p k a
  let m := (fiberPolynomial p a).rootMultiplicity b
  have hz : (fiberPolynomial p a).IsRoot b := orderedRealRoot_isRoot _ hk
  have hm : 0 < m := (Polynomial.rootMultiplicity_pos hp).mpr hz
  have hmem : parameterPoint a b ∈ multiplicityStratum p m := ⟨hp,rfl⟩
  obtain ⟨g,r,δ,hr,hδ,hga,hg,_,hchart,_⟩ := multiplicity_stratum_local_chart p hmem hm
  have hpc : q.map (MvPolynomial.eval a) ≠ 0 := by
    simpa only [q,← fiberPolynomial_eq_map] using hp
  have hkc : k < (q.map (MvPolynomial.eval a)).roots.toFinset.card := by
    simpa only [q,← fiberPolynomial_eq_map] using hk
  have hcont : ContinuousWithinAt (orderedFiberRoot p k) S a := by
    simpa only [q,← fiberPolynomial_eq_map,orderedFiberRoot] using
      parameter_ordered_root_continuousWithinAt q a hpc hkc hS
  have hmul : ∀ᶠ x in 𝓝[S] a,
      (fiberPolynomial p x).rootMultiplicity (orderedFiberRoot p k x) = m := by
    simpa only [q,← fiberPolynomial_eq_map,orderedFiberRoot,m,b] using
      parameter_ordered_root_multiplicity_locally_constant q a hpc hkc hS
  have hnear : ∀ᶠ x in 𝓝[S] a, dist (orderedFiberRoot p k x) b < δ :=
    hcont.eventually (Metric.ball_mem_nhds b hδ)
  have hbase : ∀ᶠ x in 𝓝[S] a, x ∈ Metric.ball a r :=
    Filter.mem_of_superset (nhdsWithin_le_nhds (Metric.ball_mem_nhds a hr)) (fun _ h => h)
  refine ⟨g,hg.contDiffAt (Metric.ball_mem_nhds a hr),hga,?_⟩
  filter_upwards [hbase,hnear,hmul,self_mem_nhdsWithin] with x hx hnx hmx hxS
  apply hchart x hx _ hnx
  have hcard : (fiberPolynomial p x).roots.toFinset.card = (fiberPolynomial p a).roots.toFinset.card := by
    simpa only [q,← fiberPolynomial_eq_map] using (hS hxS).2.1
  have hkx : k < (fiberPolynomial p x).roots.toFinset.card := hcard ▸ hk
  exact ⟨Polynomial.ne_zero_of_mem_roots
    (Multiset.mem_toFinset.mp (orderedRealRoot_mem _ hkx)),hmx⟩

theorem orderedFiberRoot_contDiffWithinAt
    (p : MvPolynomial (Option (Fin n)) ℝ) (a : Vec n)
    (hp : fiberPolynomial p a ≠ 0) {k : ℕ}
    (hk : k < (fiberPolynomial p a).roots.toFinset.card) {S : Set (Vec n)}
    (hS : S ⊆ rootSignatureStratum (MvPolynomial.optionEquivLeft ℝ (Fin n) p) a) :
    ContDiffWithinAt ℝ ∞ (orderedFiberRoot p k) S a := by
  obtain ⟨g,hg,hga,heq⟩ := orderedFiberRoot_local_smooth_extension p a hp hk hS
  exact hg.contDiffWithinAt.congr_of_eventuallyEq heq hga.symm

end RealAlgebraicGeometry
end BfgsVerification
