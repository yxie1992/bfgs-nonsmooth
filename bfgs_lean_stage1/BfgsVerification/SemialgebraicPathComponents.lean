import BfgsVerification.SemialgebraicSmoothPathTargets
import BfgsVerification.SemialgebraicSyntax

noncomputable section
open Set
open scoped Topology ContDiff Classical
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ]
local notation "E" => (σ → ℝ)

/-- The actual equivalence class for finite-piece-smooth paths in `S`. -/
def semialgebraicSmoothComponent (S : Set E) (x : E) : Set E :=
  {y | SemialgebraicPiecewiseSmoothPathIn S x y}

theorem semialgebraicSmoothComponent_subset (S : Set E) (x : E) :
    semialgebraicSmoothComponent S x ⊆ S := fun _ hy => hy.mem.2

theorem semialgebraicSmoothComponent_eq_of_path {S : Set E} {x y : E}
    (hxy : SemialgebraicPiecewiseSmoothPathIn S x y) :
    semialgebraicSmoothComponent S x = semialgebraicSmoothComponent S y := by
  ext z
  exact ⟨fun hxz => hxy.symm.trans hxz, fun hyz => hxy.trans hyz⟩

/-- Every point of an actual semialgebraic path has an actual semialgebraic prefix. -/
theorem SemialgebraicPiecewiseSmoothPath.prefix {S : Set E} {x y : E}
    (p : SemialgebraicPiecewiseSmoothPath S x y) {t : ℝ} (ht : t ∈ Icc 0 1) :
    SemialgebraicPiecewiseSmoothPathIn S x (p.path.curve t) := by
  classical
  by_cases ht0 : t = 0
  · subst t
    rw [p.path.source]
    exact SemialgebraicPiecewiseSmoothPathIn.refl
      (p.path.source ▸ p.path.mapsTo (by norm_num))
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hm : MapsTo (fun u : ℝ => t*u) (Icc 0 1) (Icc 0 1) := by
    intro u hu
    change 0 ≤ t*u ∧ t*u ≤ 1
    exact ⟨mul_nonneg ht.1 hu.1, (mul_le_of_le_one_right ht.1 hu.2).trans ht.2⟩
  let q : PiecewiseSmoothPath S x (p.path.curve t) := {
    curve := fun u => p.path.curve (t*u)
    continuousOn := p.path.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn hm
    source := by simpa using p.path.source
    target := by simp
    mapsTo := p.path.mapsTo.comp hm
    exceptions := p.path.exceptions.image (fun e => e/t)
    smoothAt := by
      intro u hu he
      have htu : t*u ∈ Ioo (0 : ℝ) 1 :=
        ⟨mul_pos htp hu.1, by nlinarith [ht.2, hu.2]⟩
      have hne : t*u ∉ p.path.exceptions := by
        intro h
        apply he
        exact Finset.mem_image.mpr ⟨t*u, h, by field_simp⟩
      exact (p.path.smoothAt (t*u) htu hne).comp u (contDiffAt_const.mul contDiffAt_id) }
  refine ⟨⟨q, ?_⟩⟩
  have hsa := p.semialgebraic.affine_precomp t 0 (by simpa only [add_zero] using hm)
  simpa only [add_zero] using hsa

/-- The entire enriched path lies in its source's actual enriched component. -/
theorem SemialgebraicPiecewiseSmoothPath.in_component {S : Set E} {x y : E}
    (p : SemialgebraicPiecewiseSmoothPath S x y) :
    SemialgebraicPiecewiseSmoothPathIn (semialgebraicSmoothComponent S x) x y := by
  exact ⟨⟨{ p.path with mapsTo := fun _ ht => p.prefix ht }, p.semialgebraic⟩⟩

theorem semialgebraicSmoothComponent_connected (S : Set E) (x : E) :
    SemialgebraicPiecewiseSmoothConnected (semialgebraicSmoothComponent S x) := by
  intro y hy z hz
  obtain ⟨p⟩ := hy.symm.trans hz
  have h := p.in_component
  rwa [← semialgebraicSmoothComponent_eq_of_path hy] at h

/-- Whole-piece description of each actual path component from a finite cover. -/
theorem semialgebraicSmoothComponent_eq_union_cover {m : ℕ} {S : Set E}
    (C : Fin m → Set E) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, SemialgebraicPiecewiseSmoothConnected (C i)) (x : E) :
    semialgebraicSmoothComponent S x =
      ⋃ i ∈ Finset.univ.filter (fun i => (C i ∩ semialgebraicSmoothComponent S x).Nonempty), C i := by
  classical
  have hsub : ∀ i, C i ⊆ S := by
    intro i y hy
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, hy⟩
  ext y
  constructor
  · intro hy
    have hyS := semialgebraicSmoothComponent_subset S x hy
    rw [hcover] at hyS
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyS
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, ⟨y, hi, hy⟩⟩, hi⟩⟩
  · intro hy
    obtain ⟨i, hy⟩ := mem_iUnion.mp hy
    obtain ⟨hi, hy⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzc⟩ := (Finset.mem_filter.mp hi).2
    exact hzc.trans ((hC i z hz y hy).mono (hsub i))

theorem finite_semialgebraic_path_components_of_finite_path_cover {m : ℕ} {S : Set E}
    (C : Fin m → Set E) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, SemialgebraicPiecewiseSmoothConnected (C i)) :
    (semialgebraicSmoothComponent S '' S).Finite := by
  have hsub : ∀ i, C i ⊆ S := by
    intro i y hy
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hs : ∀ i, (semialgebraicSmoothComponent S '' C i).Subsingleton := by
    intro i A hA B hB
    obtain ⟨x, hx, rfl⟩ := hA
    obtain ⟨y, hy, rfl⟩ := hB
    exact semialgebraicSmoothComponent_eq_of_path ((hC i x hx y hy).mono (hsub i))
  have h := Set.finite_iUnion (fun i => (hs i).finite)
  rwa [← image_iUnion, ← hcover] at h

theorem semialgebraicSmoothComponent_semialgebraic_of_finite_path_cover
    {τ : Type*} [Fintype τ] {m : ℕ} {S : Set (τ → ℝ)}
    (C : Fin m → Set (τ → ℝ)) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, SemialgebraicPiecewiseSmoothConnected (C i)) (hSA : ∀ i, IsSemialgebraic (C i))
    (x : τ → ℝ) : IsSemialgebraic (semialgebraicSmoothComponent S x) := by
  classical
  rw [semialgebraicSmoothComponent_eq_union_cover C hcover hC x]
  exact isSemialgebraic_finset_union _ C (fun i _ => hSA i)

end RealAlgebraicGeometry
end BfgsVerification
