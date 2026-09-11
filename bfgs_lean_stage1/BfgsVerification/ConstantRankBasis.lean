import BfgsVerification.AffineDistanceContinuity
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.ConstantRankFields
open AffineBarycentric

/-- A nonempty finite family has an actual affinely independent subfamily
with exactly the same affine span. Its indices belong to the original family. -/
theorem exists_affine_basis_indices {n m : ℕ} (g : Fin m → Vec n) (i : Fin m) :
    ∃r : ℕ,∃j : Fin r,∃a : Fin r → Fin m,
      AffineIndependent ℝ (fun q => g (a q)) ∧
      affineSpan ℝ (range (fun q => g (a q)))=affineSpan ℝ (range g) := by
  classical
  obtain ⟨S,hS,hspan,hind⟩ := exists_affineIndependent ℝ (Vec n) (range g)
  have hfinite : S.Finite := (Set.finite_range g).subset hS
  letI : Fintype S := hfinite.fintype
  have hne : S.Nonempty := (affineSpan_nonempty ℝ).mp (by
    rw [hspan]
    exact ⟨g i,mem_affineSpan ℝ (mem_range_self i)⟩)
  letI : Nonempty S := hne.to_subtype
  let r := Fintype.card S
  let e : Fin r ≃ S := (Fintype.equivFin S).symm
  let a : Fin r → Fin m := fun q => Classical.choose (hS (e q).property)
  have heq (q : Fin r) : g (a q)=(e q : Vec n) := Classical.choose_spec (hS (e q).property)
  have hselected : AffineIndependent ℝ (fun q => g (a q)) := by
    have h := hind.comp_embedding e.toEmbedding
    convert h using 1
    funext q
    exact heq q
  have hrange : range (fun q => g (a q))=S := by
    ext z
    constructor
    · rintro ⟨q,rfl⟩
      change g (a q)∈S
      rw [heq]
      exact (e q).property
    · intro hz
      refine ⟨e.symm ⟨z,hz⟩,?_⟩
      change g (a (e.symm ⟨z,hz⟩))=z
      rw [heq]
      simp
  refine ⟨r,⟨0,Fintype.card_pos⟩,a,hselected,?_⟩
  rwa [hrange]

/-- Actual constant rank and nearby independence force the fixed selected
subfamily to continue spanning the full family. Span persistence is derived. -/
theorem fixed_basis_spans_near {d n m r : ℕ} (g : Vec d → Fin m → Vec n)
    (p : Vec d) (a : Fin r → Fin m) (j : Fin r)
    (hc : ∀i,ContinuousAt (fun x => g x i) p)
    (hind : AffineIndependent ℝ (fun q => g p (a q)))
    (hspan : affineSpan ℝ (range (fun q => g p (a q)))=affineSpan ℝ (range (g p)))
    (hrank : ∀ᶠx in 𝓝 p,Module.finrank ℝ (vectorSpan ℝ (range (g x)))=
      Module.finrank ℝ (vectorSpan ℝ (range (g p)))) :
    ∀ᶠx in 𝓝 p,AffineIndependent ℝ (fun q => g x (a q)) ∧
      affineSpan ℝ (range (fun q => g x (a q)))=affineSpan ℝ (range (g x)) := by
  have he : ∀ᶠx in 𝓝 p,AffineIndependent ℝ (fun q => g x (a q)) := by
    have hh := eventually_full_column_rank (fun x => augmented (fun q => g x (a q))) p
      (augmented_continuousAt (fun x q => g x (a q)) p (fun q => hc (a q)))
      ((affineIndependent_iff_augmented_injective _).mp hind)
    exact hh.mono (fun x hx => (affineIndependent_iff_augmented_injective _).mpr hx)
  letI : Nonempty (Fin r) := ⟨j⟩
  have hcard : Fintype.card (Fin r)=Module.finrank ℝ (vectorSpan ℝ (range (g p)))+1 := by
    have h := hind.finrank_vectorSpan_add_one
    have hdir := congrArg (fun s : AffineSubspace ℝ (Vec n) => s.direction) hspan
    simp only [direction_affineSpan] at hdir
    rw [hdir] at h
    exact h.symm
  filter_upwards [he,hrank] with x hx hr
  refine ⟨hx,hx.affineSpan_eq_of_le_of_card_eq_finrank_add_one (sp := affineSpan ℝ (range (g x))) ?_ ?_⟩
  · apply affineSpan_mono
    rintro z ⟨q,rfl⟩
    exact mem_range_self (a q)
  · rw [direction_affineSpan,hr]
    exact hcard

end BfgsVerification.ConstantRankFields
