import BfgsVerification.SemialgebraicFunctionPieces

noncomputable section
open Set Filter Polynomial
open scoped Topology ContDiff
namespace BfgsVerification.RealAlgebraicGeometry

/-- A genuine semialgebraic scalar graph is smooth at every point of its
actual domain except a finite set. No continuity, differentiability, root
selection or stratification is supplied as an assumption. -/
theorem semialgebraic_scalar_smooth_except_finite {f : ℝ → ℝ} {D : Set ℝ}
    (hf : IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ D ∧ v none = f (v (some 0))}) :
    ∃ E : Finset ℝ, ∀ t ∈ D, t ∉ E → ContDiffAt ℝ ∞ f t := by
  classical
  let F : Vec 1 → ℝ := fun x => f (x 0)
  let S : Set (Vec 1) := {x | x 0 ∈ D}
  have hF : IsSemialgebraic {v : Option (Fin 1) → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = F (fun i => v (some i))} := hf
  obtain ⟨C,hC,hcover⟩ := semialgebraic_function_finite_smooth_pieces hF
  choose B hB using fun T : C =>
    vec_one_semialgebraic_neighborhood_except_finite (hC T T.2).1
  refine ⟨Finset.univ.biUnion B,?_⟩
  intro t ht htE
  have hx : (fun _ : Fin 1 => t) ∈ ⋃ T ∈ C, T := by
    rw [hcover]
    exact ht
  obtain ⟨T,hx⟩ := mem_iUnion.mp hx
  obtain ⟨hT,hxT⟩ := mem_iUnion.mp hx
  let i : C := ⟨T,hT⟩
  have htB : t ∉ B i := fun h => htE (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,h⟩)
  have hnear := hB i t hxT htB
  have hmap : ContDiff ℝ ∞ (fun u : ℝ => fun _ : Fin 1 => u) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  have hsm : ContDiffOn ℝ ∞ (fun u : ℝ => F (fun _ : Fin 1 => u))
      {u : ℝ | (fun _ : Fin 1 => u) ∈ T} :=
    (hC T hT).2.comp hmap.contDiffOn (fun _ hu => hu)
  exact hsm.contDiffAt hnear

/-- Literal interval version used in A: continuity on the whole interval,
including its endpoints, and an actual finite exceptional interior set.
The function is in fact infinitely smooth at every other interior point. -/
theorem continuous_semialgebraic_interval_piecewise_smooth {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hf : IsSemialgebraic {v : Option (Fin 1) → ℝ |
      v (some 0) ∈ Icc a b ∧ v none = f (v (some 0))}) :
    ∃ E : Finset ℝ, ContinuousOn f (Icc a b) ∧
      ∀ t ∈ Ioo a b, t ∉ E → ContDiffAt ℝ ∞ f t := by
  obtain ⟨E,hE⟩ := semialgebraic_scalar_smooth_except_finite hf
  exact ⟨E,hc,fun t ht hn => hE t ⟨ht.1.le,ht.2.le⟩ hn⟩

end BfgsVerification.RealAlgebraicGeometry
