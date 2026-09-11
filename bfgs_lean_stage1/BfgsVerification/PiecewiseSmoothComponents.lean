import BfgsVerification.SmoothCylindricalConnectivity
import BfgsVerification.SemialgebraicSyntax

noncomputable section
open Set
open scoped Topology ContDiff Classical
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual equivalence class for finite-piece-smooth paths in `S`. -/
def piecewiseSmoothComponent (S : Set E) (x : E) : Set E :=
  {y | PiecewiseSmoothPathIn S x y}

theorem piecewiseSmoothComponent_subset (S : Set E) (x : E) :
    piecewiseSmoothComponent S x ⊆ S := fun _ hy => hy.mem.2

theorem piecewiseSmoothComponent_eq_of_path {S : Set E} {x y : E}
    (hxy : PiecewiseSmoothPathIn S x y) :
    piecewiseSmoothComponent S x = piecewiseSmoothComponent S y := by
  ext z
  exact ⟨fun hxz => hxy.symm.trans hxz, fun hyz => hxy.trans hyz⟩

/-- Every point of an actual path can be reached by its reparameterized prefix. -/
theorem PiecewiseSmoothPath.prefix {S : Set E} {x y : E}
    (p : PiecewiseSmoothPath S x y) {t : ℝ} (ht : t ∈ Icc 0 1) :
    PiecewiseSmoothPathIn S x (p.curve t) := by
  classical
  by_cases ht0 : t = 0
  · subst t
    rw [p.source]
    exact PiecewiseSmoothPathIn.refl (p.source ▸ p.mapsTo (by norm_num))
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hm : MapsTo (fun u : ℝ => t*u) (Icc 0 1) (Icc 0 1) := by
    intro u hu
    change 0 ≤ t*u ∧ t*u ≤ 1
    exact ⟨mul_nonneg ht.1 hu.1, (mul_le_of_le_one_right ht.1 hu.2).trans ht.2⟩
  refine ⟨⟨fun u => p.curve (t*u), p.continuousOn.comp
    (continuous_const.mul continuous_id).continuousOn hm,
    by simpa using p.source, by simp,
    p.mapsTo.comp hm, p.exceptions.image (fun e => e/t), ?_⟩⟩
  intro u hu he
  have htu : t*u ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos htp hu.1, by nlinarith [ht.2, hu.2]⟩
  have hne : t*u ∉ p.exceptions := by
    intro h
    apply he
    exact Finset.mem_image.mpr ⟨t*u, h, by field_simp⟩
  exact (p.smoothAt (t*u) htu hne).comp u (contDiffAt_const.mul contDiffAt_id)

/-- The entire path is contained in the actual smooth-path component of its source. -/
theorem PiecewiseSmoothPath.in_component {S : Set E} {x y : E}
    (p : PiecewiseSmoothPath S x y) :
    PiecewiseSmoothPathIn (piecewiseSmoothComponent S x) x y := by
  exact ⟨{ p with mapsTo := fun _ ht => p.prefix ht }⟩

theorem piecewiseSmoothComponent_piecewiseSmoothConnected (S : Set E) (x : E) :
    PiecewiseSmoothConnected (piecewiseSmoothComponent S x) := by
  intro y hy z hz
  obtain ⟨p⟩ := hy.symm.trans hz
  have h := p.in_component
  rwa [← piecewiseSmoothComponent_eq_of_path hy] at h

/-- Whole-piece description of each actual path component from a finite cover. -/
theorem piecewiseSmoothComponent_eq_union_cover {m : ℕ} {S : Set E}
    (C : Fin m → Set E) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, PiecewiseSmoothConnected (C i)) (x : E) :
    piecewiseSmoothComponent S x =
      ⋃ i ∈ Finset.univ.filter (fun i => (C i ∩ piecewiseSmoothComponent S x).Nonempty), C i := by
  classical
  have hsub : ∀ i, C i ⊆ S := by
    intro i y hy
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, hy⟩
  ext y
  constructor
  · intro hy
    have hyS := piecewiseSmoothComponent_subset S x hy
    rw [hcover] at hyS
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyS
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, ⟨y, hi, hy⟩⟩, hi⟩⟩
  · intro hy
    obtain ⟨i, hy⟩ := mem_iUnion.mp hy
    obtain ⟨hi, hy⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzc⟩ := (Finset.mem_filter.mp hi).2
    exact hzc.trans ((hC i z hz y hy).mono (hsub i))

theorem finite_smooth_components_of_finite_smooth_cover {m : ℕ} {S : Set E}
    (C : Fin m → Set E) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, PiecewiseSmoothConnected (C i)) :
    (piecewiseSmoothComponent S '' S).Finite := by
  have hsub : ∀ i, C i ⊆ S := by
    intro i y hy
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hs : ∀ i, (piecewiseSmoothComponent S '' C i).Subsingleton := by
    intro i A hA B hB
    obtain ⟨x, hx, rfl⟩ := hA
    obtain ⟨y, hy, rfl⟩ := hB
    exact piecewiseSmoothComponent_eq_of_path ((hC i x hx y hy).mono (hsub i))
  have h := Set.finite_iUnion (fun i => (hs i).finite)
  rwa [← image_iUnion, ← hcover] at h

theorem piecewiseSmoothComponent_semialgebraic_of_finite_smooth_cover
    {σ : Type*} [Fintype σ] {m : ℕ} {S : Set (σ → ℝ)}
    (C : Fin m → Set (σ → ℝ)) (hcover : S = ⋃ i, C i)
    (hC : ∀ i, PiecewiseSmoothConnected (C i)) (hSA : ∀ i, IsSemialgebraic (C i))
    (x : σ → ℝ) : IsSemialgebraic (piecewiseSmoothComponent S x) := by
  classical
  rw [piecewiseSmoothComponent_eq_union_cover C hcover hC x]
  exact isSemialgebraic_finset_union _ C (fun i _ => hSA i)

end RealAlgebraicGeometry
end BfgsVerification
