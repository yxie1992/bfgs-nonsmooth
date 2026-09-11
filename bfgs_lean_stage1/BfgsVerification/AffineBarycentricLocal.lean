import BfgsVerification.AffineBarycentricCoordinates

/-! Module A's finite-family barycentric stability, retaining every actual
active index and deriving zero extension from affine-span membership. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace AffineBarycentric

/-- Affine zero of a subfamily supplies coefficients on the full original
index set, exactly zero at every missing index. -/
theorem affine_zero_subset_coefficients {n m : ℕ} (g : Fin m → Vec n)
    (J : Finset (Fin m)) (hzero : (0 : Vec n) ∈ affineSpan ℝ (g '' (J : Set (Fin m)))) :
    ∃ w : Vec m, (augmented g).mulVec w = affineTarget n ∧ ∀ i, i ∉ J → w i = 0 := by
  classical
  have hrange : Set.range (fun i : (J : Set (Fin m)) => g i) = g '' (J : Set (Fin m)) := by
    ext x
    simp only [mem_range, mem_image]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  have hmem : (0 : Vec n) ∈ affineSpan ℝ (Set.range (fun i : (J : Set (Fin m)) => g i)) := by
    rwa [hrange]
  obtain ⟨s, w, hw, he⟩ := (mem_affineSpan_iff_eq_affineCombination ℝ (Vec n)).mp hmem
  obtain ⟨T, hTJ, v, hv, hcomb⟩ :=
    (Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype ℝ (Vec n)).mpr ⟨s, w, hw, he⟩
  let wfull : Vec m := fun i => if i ∈ T then v i else 0
  have hwfull : (∑ i, wfull i) = 1 := by
    simpa [wfull] using hv
  have hvfull : (∑ i, wfull i • g i) = 0 := by
    rw [Finset.affineCombination_eq_linear_combination T g v hv] at hcomb
    simpa [wfull, ite_smul] using hcomb.symm
  refine ⟨wfull, (augmented_equation_iff g wfull).mpr ⟨hwfull, hvfull⟩, ?_⟩
  intro i hi
  have hiT : i ∉ T := fun h => hi (hTJ h)
  simp [wfull, hiT]

theorem augmented_continuousAt {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (x : X) (hc : ∀ i, ContinuousAt (fun p => g p i) x) :
    ContinuousAt (fun p => augmented (g p)) x := by
  have hfull : ContinuousAt g x := continuousAt_pi.mpr hc
  exact (augmented_continuous (fun g : Fin m → Vec n => g) (fun i => continuous_apply i)).continuousAt.comp hfull

/-- Exact barycentric-stability conclusion used in A and C. Near an affinely
independent family with strictly positive zero weights, any subfamily whose
affine hull contains zero must be the full family and contain zero convexly.
Only continuity at the base point is needed. -/
theorem affine_critical_subfamily_eventually_full {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (xstar : X)
    (hc : ∀ i, ContinuousAt (fun x => g x i) xstar)
    (hind : AffineIndependent ℝ (g xstar)) (wstar : Vec m)
    (hpos : ∀ i, 0 < wstar i) (hsum : (∑ i, wstar i) = 1)
    (hzero : (∑ i, wstar i • g xstar i) = 0) :
    ∀ᶠ p in 𝓝 xstar, AffineIndependent ℝ (g p) ∧ ∀ J : Finset (Fin m),
      (0 : Vec n) ∈ affineSpan ℝ (g p '' (J : Set (Fin m))) →
        J = Finset.univ ∧ (0 : Vec n) ∈ convexHull ℝ (g p '' (J : Set (Fin m))) := by
  have hA := (affineIndependent_iff_augmented_injective (g xstar)).mp hind
  have he := (augmented_equation_iff (g xstar) wstar).mpr ⟨hsum, hzero⟩
  filter_upwards [positive_solutions_eventually (fun x => augmented (g x)) xstar
    (augmented_continuousAt g xstar hc) hA (affineTarget n) wstar he hpos] with p hp
  refine ⟨(affineIndependent_iff_augmented_injective (g p)).mpr hp.1, ?_⟩
  intro J hJ
  obtain ⟨w, hw, hwJ⟩ := affine_zero_subset_coefficients (g p) J hJ
  have hwpos := (hp.2 w hw).2
  have hfull : J = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have hwi := hwJ i hi
    have hpi := hwpos i
    rw [hwi] at hpi
    exact lt_irrefl 0 hpi
  refine ⟨hfull, ?_⟩
  have h := zero_mem_convexHull_of_positive_augmented_solution (g p) w hwpos hw
  simpa only [hfull, Finset.coe_univ, Set.image_univ] using h

end AffineBarycentric
end BfgsVerification
