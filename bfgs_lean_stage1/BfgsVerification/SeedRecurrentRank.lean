import BfgsVerification.AlgebraicSeedFailure
import BfgsVerification.HomogeneousCardinality

noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter
namespace BfgsVerification.SeedOrbit
open SeedCycle AlgebraicSeed

/-- Every phase of the actual three-cycle recurs arbitrarily late. -/
theorem actual_recurrent_gradients : Homogeneous.recurrentValues orbitGradient =
    range (gradient seedC seedD) := by
  ext v
  constructor
  · intro hv
    obtain ⟨k,hk⟩ := (Homogeneous.recurrentValues_subset_range orbitGradient hv)
    exact ⟨phase k,hk⟩
  · rintro ⟨j,rfl⟩
    apply frequently_atTop.2
    intro N
    refine ⟨3*N+j.val,by omega,?_⟩
    change gradient seedC seedD (phase (3*N+j.val))=gradient seedC seedD j
    apply congrArg (gradient seedC seedD)
    apply Fin.ext
    dsimp [phase]
    omega

theorem seed_gradient_injective : Function.Injective (gradient seedC seedD) := by
  intro i j h
  have hc := root_tight_box.1.1
  have hcU := root_tight_box.1.2
  have hd := root_tight_box.2.2
  have he := congrArg (fun v : Vec 2 => v 0) h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [gradient,g0,g1,g2] at he
  all_goals exfalso; linarith

theorem actual_recurrent_cardinality : (Homogeneous.recurrentValues orbitGradient).ncard=3 := by
  rw [actual_recurrent_gradients,← image_univ]
  rw [ncard_image_of_injective univ seed_gradient_injective]
  rw [ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin]

/-- The actual first two recurrent slopes span the entire plane. -/
theorem actual_recurrent_span : Submodule.span ℝ (Homogeneous.recurrentValues orbitGradient)=⊤ := by
  rw [actual_recurrent_gradients]
  apply top_unique
  intro v _
  have h0 : gradient seedC seedD 0∈Submodule.span ℝ (range (gradient seedC seedD)) :=
    Submodule.subset_span (mem_range_self 0)
  have h1 : gradient seedC seedD 1∈Submodule.span ℝ (range (gradient seedC seedD)) :=
    Submodule.subset_span (mem_range_self 1)
  have he : v=(v 0-8*v 1) • gradient seedC seedD 0+(-8*v 1) • gradient seedC seedD 1 := by
    ext i
    fin_cases i <;> norm_num [gradient,g0,g1] <;> ring
  rw [he]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1)

theorem actual_recurrent_rank : Module.finrank ℝ
    (Submodule.span ℝ (Homogeneous.recurrentValues orbitGradient))=2 := by
  rw [actual_recurrent_span,finrank_top]
  simp [Vec,Module.finrank_pi]

/-- Actual unmodified BFGS attains H's r+1 recurrent-gradient lower bound. -/
def SharpRecurrentCardinalityTarget : Prop :=
  ∀ c₁ c₂ : ℝ,∀ hc₁ : 0<c₁,∀ hc₁' : c₁≤1/3,∀ hc : c₁<c₂,∀ hc₂ : c₂<1,
    let R := run c₁ c₂ hc₁ hc₁' hc hc₂
    R.H 0=1 ∧ Tendsto R.x atTop (𝓝 0) ∧
    Tendsto (fun k => objective seedC seedD (R.x k)) atTop (𝓝 0) ∧
    (∀k,0<objective seedC seedD (R.x k)) ∧
    (0 : Vec 2)∉ConvexSubdifferential.subdifferential (objective seedC seedD) 0 ∧
    (Homogeneous.recurrentValues R.g).ncard=3 ∧
    Module.finrank ℝ (Submodule.span ℝ (Homogeneous.recurrentValues R.g))=2 ∧
    Module.finrank ℝ (Submodule.span ℝ (Homogeneous.recurrentValues R.g))+1=
      (Homogeneous.recurrentValues R.g).ncard

theorem sharpRecurrentCardinality : SharpRecurrentCardinalityTarget := by
  intro c₁ c₂ hc₁ hc₁' hc hc₂
  obtain ⟨hI,hx,hv,hpos,_,hn⟩ := actual_run_failure hc₁ hc₁' hc hc₂
  exact ⟨hI,hx,hv,hpos,hn,actual_recurrent_cardinality,actual_recurrent_rank,
    by change Module.finrank ℝ (Submodule.span ℝ (Homogeneous.recurrentValues orbitGradient))+1=
         (Homogeneous.recurrentValues orbitGradient).ncard
       rw [actual_recurrent_rank,actual_recurrent_cardinality]⟩

end BfgsVerification.SeedOrbit
