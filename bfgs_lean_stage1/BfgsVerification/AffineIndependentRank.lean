import BfgsVerification.RateChartData

noncomputable section
open scoped BigOperators Topology ContDiff
open Matrix Filter Set
namespace BfgsVerification.ConstantRankFields
open AffineBarycentric AffineCriticalObjective ConvexSubdifferential

/-- Affine independence of the actual full family is an open condition and
forces local constancy of the actual gradient-difference matrix rank. -/
theorem locally_constant_rank_of_affineIndependent {d n m : ℕ}
    (g : Vec d → Fin m → Vec n) (p : Vec d) (i : Fin m)
    (hc : ∀j,ContinuousAt (fun x => g x j) p)
    (hind : AffineIndependent ℝ (g p)) : ∀ᶠx in 𝓝 p,
      (differenceMatrix (g x) i).rank=(differenceMatrix (g p) i).rank := by
  letI : Nonempty (Fin m) := ⟨i⟩
  have he : ∀ᶠx in 𝓝 p,AffineIndependent ℝ (g x) := by
    have hh := eventually_full_column_rank (fun x => augmented (g x)) p
      (augmented_continuousAt g p hc)
      ((affineIndependent_iff_augmented_injective _).mp hind)
    exact hh.mono (fun x hx => (affineIndependent_iff_augmented_injective _).mpr hx)
  filter_upwards [he] with x hx
  simp only [differenceMatrix_rank]
  exact Nat.add_right_cancel (hx.finrank_vectorSpan_add_one.trans hind.finrank_vectorSpan_add_one.symm)

/-- The source's sufficient affine-independence hypothesis applies to the
original active indices, including their actual gradients. -/
theorem active_affineIndependent_implies_locallyConstantActiveRank {n m : ℕ}
    {F : Vec n → ℝ} {f : Fin m → Vec n → ℝ} {p : Vec n}
    (hrep : LocalFiniteMax F f p) (hf : ∀j,ContDiffAt ℝ 2 (f j) p)
    (hind : AffineIndependent ℝ (fun j : Fin (activeIndices F f p).card =>
      coordinateGradient (f (activeIndexMap F f p j)) p)) :
    LocallyConstantActiveRank F f p := by
  have hpos : 0<(activeIndices F f p).card := (activeIndices_nonempty hrep).card_pos
  let i : Fin (activeIndices F f p).card := ⟨0,hpos⟩
  exact ⟨i,locally_constant_rank_of_affineIndependent _ p i
    (fun j => (coordinateGradient_contDiffAt (hf (activeIndexMap F f p j))).continuousAt) hind⟩

end BfgsVerification.ConstantRankFields
