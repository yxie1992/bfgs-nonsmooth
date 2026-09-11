import BfgsVerification.FiniteMaxLocalCorrectness
import BfgsVerification.SubdifferentialDifferentiability

noncomputable section
open scoped BigOperators Topology
open Set Filter BfgsVerification BfgsVerification.ConvexSubdifferential

/- Finite convexity alone gives a nonempty compact convex actual support set. -/
example {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (x : Vec n) :
    {g | Homogeneous.Supports F x g}.Nonempty ∧
      IsCompact {g | Homogeneous.Supports F x g} ∧
      Convex ℝ {g | Homogeneous.Supports F x g} :=
  ⟨subdifferential_nonempty hF x, isCompact_subdifferential hF x,
    convex_subdifferential F x⟩

/- This contract uses the full definition of a local finite maximum, with no
branch-convexity, global representation, or assumed subdifferential formula. -/
example {n m : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n} {x : Vec n}
    (hrep : ∀ᶠ z in 𝓝 x, (∃ i, f i z = F z) ∧ ∀ i, f i z ≤ F z)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x) :
    {a | Homogeneous.Supports F x a} =
      convexHull ℝ (g '' {i | f i x = F x}) := by
  have hr : LocalFiniteMax F f x := by
    filter_upwards [hrep] with z hz
    exact ⟨hz.1, fun _ ⟨i, hi⟩ => hi ▸ hz.2 i⟩
  have heq : (activeIndices F f x : Set (Fin m)) = {i | f i x = F x} := by
    ext i
    exact mem_activeIndices
  simpa only [heq] using subdifferential_eq_active_convexHull hF hr hg

/- A singleton support set identifies the actual derivative; there is no
selection continuity premise. -/
example {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) {x g : Vec n} :
    {a | Homogeneous.Supports F x a} = {g} ↔
      HasFDerivAt F (gradientFunctional g) x :=
  subdifferential_eq_singleton_iff_hasFDerivAt hF

/- Original inactive branches are removed inside the theorem. -/
example {n m : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {f : Fin m → Vec n → ℝ} (g : Vec n → Fin m → Vec n) (xstar : Vec n)
    (hrep : LocalFiniteMax F f xstar)
    (hg : ∀ᶠ p in 𝓝 xstar, ∀ i, HasFDerivAt (f i) (gradientFunctional (g p i)) p)
    (hc : ∀ i, ContinuousAt (fun p => g p i) xstar)
    (hind : AffineIndependent ℝ (fun i => g xstar (activeIndexMap F f xstar i)))
    (w : Vec (activeIndices F f xstar).card)
    (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1)
    (hzero : (∑ i, w i • g xstar (activeIndexMap F f xstar i)) = 0) :
    ∀ᶠ p in 𝓝 xstar,
      ((0 : Vec n) ∈ affineSpan ℝ {a | Homogeneous.Supports F p a} ↔ ∀ z, F p ≤ F z) :=
  local_affine_critical_correctness_original_family hF g xstar hrep hg hc hind w hw hsum hzero

#check @exists_distinct_supports_of_not_differentiableAt
#check @isClosed_graph
