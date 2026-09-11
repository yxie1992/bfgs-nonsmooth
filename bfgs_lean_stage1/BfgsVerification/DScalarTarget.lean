import BfgsVerification.DScalarAssembly

open Set Filter
open scoped Topology

namespace BfgsVerification.DScalar
open DScalarGeometric
noncomputable section

/-- The actual scalar functions used by D, with their printed formulas, jets and constants. -/
theorem scalar_function_contract {b : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) :
    ContDiff ℝ 2 (phi b) ∧ ConvexOn ℝ univ (phi b) ∧
    (∀ x, 0 ≤ phi b x) ∧ (∀ x, phi b x=0 ↔ x=0) ∧
    Tendsto (phi b) (cocompact ℝ) atTop ∧ (∀ a, IsCompact {x : ℝ | phi b x ≤ a}) ∧
    (∀ x, HasDerivAt (phi b) (phiFirst b x) x) ∧
    (∀ x, HasDerivAt (phiFirst b) (phiSecond b x) x) ∧
    (∀ x, 0 ≤ deriv (deriv (phi b)) x ∧ deriv (deriv (phi b)) x ≤ max 6 (102/b)) ∧
    LipschitzWith ⟨max 6 (139264/(5*b^2)), le_trans (by norm_num) (le_max_left _ _)⟩
      (deriv (deriv (phi b))) ∧
    (∀ m, phi b (b*scale m)=(scale m)^3 ∧ HasDerivAt (phi b) ((scale m)^2) (b*scale m) ∧
      HasDerivAt (deriv (phi b)) 0 (b*scale m)) ∧
    (∀ m h, |h| ≤ scale m/2 → phi b (b*scale m+h)=(scale m)^3+(scale m)^2*h) ∧
    (∀ x, x ≤ -1 → phi b x=1-3*(x+1)+3*(x+1)^2) ∧
    (∀ x, -1 ≤ x → x ≤ 0 → phi b x= -x^3) ∧
    (∀ x, b ≤ x → phi b x=1+x-b) ∧
    (∀ m x, b*theta*scale m ≤ x → x ≤ b*scale m →
      phi b x=(theta*scale m)^3+b*(scale m)^3*(1-theta)*
        (theta^2*coordinate b (scale m) x+
          (1-theta^2)*DScalarRamp.primitive b (coordinate b (scale m) x))) := by
  exact ⟨phi_contDiff hl hr, phi_convex hl hr, phi_nonnegative hl hr, phi_zero_iff hl hr,
    phi_coercive hl hr, phi_sublevels_compact hl hr, phi_hasDerivAt hl hr, phiFirst_hasDerivAt hl,
    phi_second_derivative_bounds hl hr, phi_second_derivative_lipschitz hl hr,
    fun m => ⟨phi_node hl hr m, phi_node_hasDerivAt hl hr m, phi_node_second_hasDerivAt hl hr m⟩,
    fun m _ hh => phi_plateau hl hr m hh, fun _ hx => phi_eq_negative_quadratic hl hr hx,
    fun _ hxlo hxhi => phi_eq_negative_cubic hl hr hxlo hxhi, fun _ hx => phi_eq_outer hl hr hx,
    fun m _ hxlo hxhi => phi_interval hl hr m hxlo hxhi⟩

end
end BfgsVerification.DScalar
