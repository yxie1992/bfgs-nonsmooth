import BfgsVerification.AffineDistanceFormula

/-! Continuity of the actual affine-hull distance at each independent nonempty
family. Full rank is derived in a neighborhood, never imposed on a matrix sequence. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification
namespace AffineDistance
open AffineBarycentric AffineCriticalGeometry

theorem formulaPoint_continuousAt {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (x : X) (i : Fin m)
    (hc : ∀ j, ContinuousAt (fun p => g p j) x) (hg : AffineIndependent ℝ (g x)) :
    ContinuousAt (fun p => formulaPoint (g p)) x := by
  have hA := augmented_continuousAt g x hc
  have hK : ContinuousAt (fun p => gram (augmented (g p))) x := gram_continuous.continuousAt.comp hA
  have hd := (gram_posDef (augmented (g x)) ((affineIndependent_iff_augmented_injective _).mp hg)).det_pos.ne'
  have hi : ContinuousAt (fun p => (gram (augmented (g p)))⁻¹) x :=
    (continuousAt_matrix_inv _ (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd)).comp hK
  have hmul : Continuous (fun p : Mat m × Vec m => p.1.mulVec p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hv : ContinuousAt (fun p => inverseOnes (g p)) x :=
    hmul.continuousAt.comp (hi.prodMk_nhds continuousAt_const)
  have hden : ContinuousAt (fun p => denominator (g p)) x := by
    apply tendsto_finset_sum
    intro j _
    exact (continuous_apply j).continuousAt.comp hv
  have hw : ContinuousAt (fun p => weights (g p)) x :=
    (hden.inv₀ (denominator_pos (g x) i hg).ne').smul hv
  apply tendsto_finset_sum
  intro j _
  exact ((continuous_apply j).continuousAt.comp hw).smul
    ((PiLp.continuous_equiv_symm (p := 2) (β := fun _ : Fin n => ℝ)).continuousAt.comp (hc j))

theorem affine_distance_continuousAt {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (g : X → Fin m → Vec n) (x : X) (i : Fin m)
    (hc : ∀ j, ContinuousAt (fun p => g p j) x) (hg : AffineIndependent ℝ (g x)) :
    ContinuousAt (fun p => Metric.infDist (0 : EuclideanSpace ℝ (Fin n))
      (affineSpan ℝ (range (fun j => euclideanVector (g p j))) : Set _)) x := by
  have he : ∀ᶠ p in 𝓝 x, AffineIndependent ℝ (g p) := by
    have h := eventually_full_column_rank (fun p => augmented (g p)) x (augmented_continuousAt g x hc)
      ((affineIndependent_iff_augmented_injective _).mp hg)
    exact h.mono (fun p hp => (affineIndependent_iff_augmented_injective _).mpr hp)
  apply (formulaPoint_continuousAt g x i hc hg).norm.congr_of_eventuallyEq
  exact he.mono (fun p hp => affine_distance_eq_formula (g p) i hp)

end AffineDistance
end BfgsVerification
