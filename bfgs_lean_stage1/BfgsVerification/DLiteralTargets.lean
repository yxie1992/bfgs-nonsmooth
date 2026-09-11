import BfgsVerification.DNonStrictObjectives

noncomputable section
namespace BfgsVerification.DLiteralTargets
open SeedOrbit SeedCycle

/-- Exact source polynomial equivalence and the two printed affine consequences. -/
def LiteralIdentitiesTarget : Prop :=
  (∀x : Vec 2, ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius →
    (AlgebraicSeed.P x=0 ↔ beta (x 0) (x 1)=1/4 ∧ gamma (x 0) (x 1)=1/16)) ∧
  (0 : Vec 2) ∉ convexHull ℝ (Set.range (gradient seedC seedD)) ∧
  ((0 : ℝ)<8/17 ∧ (0 : ℝ)<1/17 ∧ (8/17 : ℝ)+8/17+1/17=1) ∧
  (∀x : Vec 2, (8/17 : ℝ)*coerciveFamily.branch 0 x+(8/17 : ℝ)*coerciveFamily.branch 1 x+
    (1/17 : ℝ)*coerciveFamily.branch 3 x = -1)

theorem literalIdentities : LiteralIdentitiesTarget :=
  ⟨fun _ hx => DLiteralIdentities.original_box_polynomial_iff hx,
    DLiteralIdentities.zero_not_mem_gradient_hull,DLiteralIdentities.coercive_weights_convex,
    DLiteralIdentities.coercive_exact_affine_combination⟩

/-- Replacing both strict tests by their literal non-strict inequalities returns
exactly the same finite histories and lengths for all three actual source runs. -/
def NonStrictRunTarget : Prop :=
  ∀c₁ c₂ : ℝ, ∀hc₁ : 0 < c₁, ∀hc₁' : c₁ ≤ 1/3, ∀hc : c₁ < c₂, ∀hc₂ : c₂ < 1,
  (let R := SeedOrbit.run c₁ c₂ hc₁ hc₁' hc hc₂
   ∀k : ℕ,
    NonStrictLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5 =
      (some (R.α k),trialHistory (phase k)) ∧
    NonStrictLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric (objective seedC seedD) (R.x k) (R.H k) c₁ c₂ 5) ∧
  (let R := coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
   ∀k : ℕ,
    NonStrictLineSearch.fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5 =
      (some (R.α k),trialHistory (phase k)) ∧
    NonStrictLineSearch.fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5) ∧
  (∀n : ℕ, ∀hn : 1 ≤ n,
   let R := DEmbedding.run hn c₁ c₂ hc₁ hc₁' hc hc₂
   ∀k : ℕ,
    NonStrictLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5 =
      (some (R.α k),trialHistory (phase k)) ∧
    NonStrictLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5 =
      DeterministicLineSearch.fromMetric DEmbedding.objective (R.x k) (R.H k) c₁ c₂ 5)

theorem nonStrictRun : NonStrictRunTarget := by
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  refine ⟨?_,?_,?_⟩
  · dsimp only
    intro k
    have he := DNonStrictObjectives.seed_fromMetric hc₁ hc₁' (hc₁.trans hc) k
    exact ⟨he,he.trans (orbit_search hc₁ hc₁' (hc₁.trans hc) k).symm⟩
  · dsimp only
    intro k
    have he := DNonStrictObjectives.coercive_fromMetric hc₁ hc₁' (hc₁.trans hc) k
    exact ⟨he,he.trans (coercive_orbit_search hc₁ hc₁' (hc₁.trans hc) k).symm⟩
  · intro n hn
    dsimp only
    intro k
    exact ⟨DNonStrictObjectives.embedding_fromMetric hn hc₁ hc₁' hc hc₂ k,
      DNonStrictObjectives.embedding_same_search hn hc₁ hc₁' hc hc₂ k⟩

end BfgsVerification.DLiteralTargets
