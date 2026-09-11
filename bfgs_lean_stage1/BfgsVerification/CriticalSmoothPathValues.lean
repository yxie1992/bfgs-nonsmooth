import BfgsVerification.SemialgebraicCriticalTargets
import BfgsVerification.SemialgebraicSmoothComponents

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace BfgsVerification.RealAlgebraicGeometry
open AffineCriticalObjective AffineSupportPath

/-- The actual piecewise-smooth path classes in C's tame alternative have
finite family, semialgebraic classes, internal smooth paths and one value. -/
theorem semialgebraic_affine_critical_smooth_components {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F) :
    (piecewiseSmoothComponent {z | IsAffineCritical F z} '' {z | IsAffineCritical F z}).Finite ∧
    ∀ x, IsSemialgebraic (piecewiseSmoothComponent {z | IsAffineCritical F z} x) ∧
      PiecewiseSmoothConnected (piecewiseSmoothComponent {z | IsAffineCritical F z} x) ∧
      ∀ p ∈ piecewiseSmoothComponent {z | IsAffineCritical F z} x,
        ∀ q ∈ piecewiseSmoothComponent {z | IsAffineCritical F z} x, F p = F q := by
  obtain ⟨hfin,hcomp⟩ := semialgebraic_smooth_components (affineCritical_set_semialgebraic hSA)
  refine ⟨hfin,fun x => ⟨(hcomp x).1,(hcomp x).2,?_⟩⟩
  intro p hp q hq
  have h := image_subsingleton_of_preconnected_finite_image
    (hcomp x).2.isPreconnected (convex_continuous hF).continuousOn
    ((semialgebraic_affine_critical_values hF hSA).subset
      (image_subset F (piecewiseSmoothComponent_subset _ x)))
  exact h ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩

/-- Every actual smooth path in the critical set has constant objective value;
no differentiability of the composed objective is assumed. -/
theorem semialgebraic_affine_critical_path_constant {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F) {x y : Vec n}
    (p : PiecewiseSmoothPath {z | IsAffineCritical F z} x y) :
    ∀ t ∈ Icc (0 : ℝ) 1, F (p.curve t) = F x := by
  intro t ht
  have hx : x ∈ piecewiseSmoothComponent {z | IsAffineCritical F z} x :=
    PiecewiseSmoothPathIn.refl (p.source ▸ p.mapsTo (by norm_num))
  exact (semialgebraic_affine_critical_smooth_components hF hSA).2 x |>.2.2
    (p.curve t) (p.prefix ht) x hx

/-- The value along any such actual path has zero derivative at every interior
parameter, including any exceptional nonsmooth parameters of the point curve. -/
theorem semialgebraic_affine_critical_path_hasDerivAt_zero {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (hSA : IsSemialgebraicObjective F) {x y : Vec n}
    (p : PiecewiseSmoothPath {z | IsAffineCritical F z} x y) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt (fun u => F (p.curve u)) 0 t := by
  apply (hasDerivAt_const t (F x)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
  exact semialgebraic_affine_critical_path_constant hF hSA p u hu

end BfgsVerification.RealAlgebraicGeometry
