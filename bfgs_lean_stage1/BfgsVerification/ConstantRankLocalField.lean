import BfgsVerification.AffineGramSmooth
import BfgsVerification.ConstantRankBasis
import Mathlib.Data.Matrix.Rank

noncomputable section
open scoped BigOperators Topology ContDiff InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification.ConstantRankFields
open AffineBarycentric AffineDistance AffineCriticalGeometry

/-- The actual columns are every gradient difference with one fixed base
member, including its zero column. -/
def differenceMatrix {n m : ℕ} (g : Fin m → Vec n) (i : Fin m) :
    Matrix (Fin n) (Fin m) ℝ := fun a j => g j a-g i a

theorem differenceMatrix_rank {n m : ℕ} (g : Fin m → Vec n) (i : Fin m) :
    (differenceMatrix g i).rank=Module.finrank ℝ (vectorSpan ℝ (range g)) := by
  rw [Matrix.rank_eq_finrank_span_cols,vectorSpan_range_eq_span_range_vsub_right ℝ g i]
  rfl

theorem euclidean_affineSpan_eq {n m r : ℕ} {g : Fin m → Vec n} {h : Fin r → Vec n}
    (he : affineSpan ℝ (range g)=affineSpan ℝ (range h)) :
    affineSpan ℝ (range (fun i => euclideanVector (g i)))=
      affineSpan ℝ (range (fun i => euclideanVector (h i))) := by
  let e : Vec n →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Vec n)).symm.toLinearMap.toAffineMap
  have hh := congrArg (fun s : AffineSubspace ℝ (Vec n) => s.map e) he
  simpa only [AffineSubspace.map_span,← Set.range_comp,Function.comp_def] using hh

theorem closest_eq_of_affineSpan_eq {n : ℕ} {α β : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (h : β → EuclideanSpace ℝ (Fin n))
    (i : α) (j : β) (he : affineSpan ℝ (range g)=affineSpan ℝ (range h)) :
    closestAffinePoint g i=closestAffinePoint h j := by
  apply eq_closest_of_pairings h j
  · rw [← he]
    exact closestAffinePoint_mem_affineSpan g i
  · intro a
    apply affine_pairing_closest
    rw [he]
    exact mem_affineSpan ℝ (mem_range_self a)

/-- Constant rank of the actual gradient-difference matrix implies regularity
of the actual minimum-norm point of the full affine hull. A persistent basis is
selected and proved to span; it is not an additional hypothesis. -/
theorem closest_contDiffAt_of_constant_rank {d n m : ℕ} {k : WithTop ℕ∞}
    (g : Vec d → Fin m → Vec n) (p : Vec d) (i : Fin m)
    (hc : ∀j,ContDiffAt ℝ k (fun x => g x j) p)
    (hrank : ∀ᶠx in 𝓝 p,(differenceMatrix (g x) i).rank=(differenceMatrix (g p) i).rank) :
    ContDiffAt ℝ k (fun x => closestAffinePoint (fun j => euclideanVector (g x j)) i) p := by
  obtain ⟨r,j,a,hind,hspan⟩ := exists_affine_basis_indices (g p) i
  have he := fixed_basis_spans_near g p a j (fun j => (hc j).continuousAt) hind hspan
    (by simpa only [differenceMatrix_rank] using hrank)
  have hs := formulaPoint_contDiffAt (fun x q => g x (a q)) j (fun q => hc (a q)) hind
  apply hs.congr_of_eventuallyEq
  filter_upwards [he] with x hx
  rw [formulaPoint_eq_closest _ j hx.1]
  exact (closest_eq_of_affineSpan_eq (fun q => euclideanVector (g x (a q)))
    (fun q => euclideanVector (g x q)) j i (euclidean_affineSpan_eq hx.2)).symm

/-- Canonical positive common-rate field of the actual full affine hull. -/
def commonRate {n m : ℕ} (g : Fin m → Vec n) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  (‖closestAffinePoint (fun j => euclideanVector (g j)) i‖^2)⁻¹ •
    closestAffinePoint (fun j => euclideanVector (g j)) i

theorem commonRate_pairing {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hne : closestAffinePoint (fun j => euclideanVector (g j)) i≠0) (j : Fin m) :
    ⟪euclideanVector (g j),commonRate g i⟫_ℝ=1 := by
  have hn : ‖closestAffinePoint (fun j => euclideanVector (g j)) i‖^2≠0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
  have hp := affine_pairing_closest (fun q => euclideanVector (g q)) i
    (euclideanVector (g j)) (mem_affineSpan ℝ (mem_range_self j))
  rw [commonRate,inner_smul_right,hp]
  exact inv_mul_cancel₀ hn

theorem commonRate_contDiffAt_of_constant_rank {d n m : ℕ} {k : WithTop ℕ∞}
    (g : Vec d → Fin m → Vec n) (p : Vec d) (i : Fin m)
    (hc : ∀j,ContDiffAt ℝ k (fun x => g x j) p)
    (hrank : ∀ᶠx in 𝓝 p,(differenceMatrix (g x) i).rank=(differenceMatrix (g p) i).rank)
    (hzero : (0 : EuclideanSpace ℝ (Fin n))∉affineSpan ℝ (range (fun j => euclideanVector (g p j)))) :
    ContDiffAt ℝ k (fun x => commonRate (g x) i) p := by
  have ha := closest_contDiffAt_of_constant_rank g p i hc hrank
  have hne : closestAffinePoint (fun j => euclideanVector (g p j)) i≠0 :=
    fun he => hzero ((closestAffinePoint_zero_iff _ i).mp he)
  exact ((ha.norm_sq ℝ).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))).smul ha

/-- Under C1 gradient regularity, the actual common-rate field is C1 on one
open neighborhood and pairs to one with every member of the fixed family. -/
theorem commonRate_chart {d n m : ℕ} (g : Vec d → Fin m → Vec n)
    (p : Vec d) (i : Fin m)
    (hc : ∀j,ContDiffAt ℝ 1 (fun x => g x j) p)
    (hrank : ∀ᶠx in 𝓝 p,(differenceMatrix (g x) i).rank=(differenceMatrix (g p) i).rank)
    (hzero : (0 : EuclideanSpace ℝ (Fin n))∉affineSpan ℝ (range (fun j => euclideanVector (g p j)))) :
    ∃U : Set (Vec d),IsOpen U ∧ p∈U ∧
      ContDiffOn ℝ 1 (fun x => commonRate (g x) i) U ∧
      ∀x∈U,∀j,⟪euclideanVector (g x j),commonRate (g x) i⟫_ℝ=1 := by
  have ha := closest_contDiffAt_of_constant_rank g p i hc hrank
  have hv := commonRate_contDiffAt_of_constant_rank g p i hc hrank hzero
  have hne : closestAffinePoint (fun j => euclideanVector (g p j)) i≠0 :=
    fun he => hzero ((closestAffinePoint_zero_iff _ i).mp he)
  have he : ∀ᶠx in 𝓝 p,closestAffinePoint (fun j => euclideanVector (g x j)) i≠0 :=
    ha.continuousAt.eventually_ne hne
  obtain ⟨U,hUn,hU,hp⟩ := mem_nhds_iff.mp ((hv.eventually (by norm_num)).and he)
  refine ⟨U,hU,hp,fun x hx => (hUn hx).1.contDiffWithinAt,?_⟩
  intro x hx j
  exact commonRate_pairing _ i (hUn hx).2 j

end BfgsVerification.ConstantRankFields
