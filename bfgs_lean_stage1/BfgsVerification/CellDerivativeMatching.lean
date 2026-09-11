import BfgsVerification.ConvexCellRadial
import BfgsVerification.AffineProjection

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.ConvexCellRadial

/-- The full-gradient boundary assertion from the source proof. Unlike the
radial convergence route, this exact assertion uses a full-dimensional cell. -/
theorem full_derivative_eq_on_cell {n : ℕ} {F f : Vec n → ℝ}
    {P U : Set (Vec n)} (hP : Convex ℝ P) (hfull : (interior P).Nonempty)
    (hU : IsOpen U) {x : Vec n} (hxP : x ∈ P) (hxU : x ∈ U)
    (hrep : ∀ z ∈ U, z ∈ P → F z = f z)
    {g h : Vec n →L[ℝ] ℝ} (hg : HasFDerivAt F g x) (hh : HasFDerivAt f h x) :
    g = h := by
  have heq : F =ᶠ[𝓝[P] x] f := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU),self_mem_nhdsWithin]
      with z hzU hzP
    exact hrep z hzU hzP
  exact (uniqueDiffOn_convex hP hfull x hxP).eq hg.hasFDerivWithinAt
    (hh.hasFDerivWithinAt.congr_of_eventuallyEq heq (hrep x hxU hxP))

theorem actual_gradients_eq_on_cell {n : ℕ} {F f : Vec n → ℝ}
    {P U : Set (Vec n)} (hP : Convex ℝ P) (hfull : (interior P).Nonempty)
    (hU : IsOpen U) {x : Vec n} (hxP : x ∈ P) (hxU : x ∈ U)
    (hrep : ∀ z ∈ U, z ∈ P → F z = f z) {g h : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt f (gradientFunctional h) x) : g = h :=
  AffineProjection.gradientFunctional_injective
    (full_derivative_eq_on_cell hP hfull hU hxP hxU hrep hg hh)

end BfgsVerification.ConvexCellRadial
