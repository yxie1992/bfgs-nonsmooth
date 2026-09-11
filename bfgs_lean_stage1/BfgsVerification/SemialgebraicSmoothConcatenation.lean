import BfgsVerification.SemialgebraicSmoothPaths
import BfgsVerification.SemialgebraicCurveJoining

noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ]

theorem SemialgebraicPiecewiseSmoothPathIn.trans {S : Set (σ → ℝ)} {x y z : σ → ℝ}
    (hxy : SemialgebraicPiecewiseSmoothPathIn S x y)
    (hyz : SemialgebraicPiecewiseSmoothPathIn S y z) :
    SemialgebraicPiecewiseSmoothPathIn S x z := by
  obtain ⟨p⟩ := hxy
  obtain ⟨q⟩ := hyz
  exact ⟨⟨concatenatedSmoothPath p.path q.path,
    p.semialgebraic.joinedCurve q.semialgebraic⟩⟩

end RealAlgebraicGeometry
end BfgsVerification
