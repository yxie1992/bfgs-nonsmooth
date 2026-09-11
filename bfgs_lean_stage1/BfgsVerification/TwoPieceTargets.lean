import BfgsVerification.TwoPieceProjection

noncomputable section
open Set Filter
namespace BfgsVerification.TwoPieceBudget

/-- Literal finite termination means well-foundedness of all actual accepted
choices and a finitely reachable terminal search direction unbounded below. -/
def TwoPieceTerminationTarget : Prop :=
  ConvexOn ℝ univ objective ∧
  ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → c₂ < 1 →
    WellFounded (fun T S => Step c₁ c₂ S T) ∧
    ∀ S : State, ∃ T : State, Relation.ReflTransGen (Step c₁ c₂) S T ∧
      (¬∃ U : State, Step c₁ c₂ T U) ∧
      Tendsto (fun t : ℝ => objective (T.x+bfgsStep T.H T.g t)) atTop atBot

theorem twoPieceTermination : TwoPieceTerminationTarget := by
  refine ⟨objective_convex,?_⟩
  intro c₁ c₂ hc₁ hc hc₂
  refine ⟨wellFounded_actual_steps hc₁ hc hc₂,?_⟩
  intro S
  obtain ⟨T,ht,hend⟩ := finite_path_to_terminal hc₁ hc hc₂ S
  exact ⟨T,ht,hend,terminal_direction_unbounded hc₁ hc hc₂ T hend⟩

def TwoPieceLinearImageTarget : Prop :=
  (∀ {n : ℕ} (Q : Matrix (Fin 2) (Fin n) ℝ), AffineProjection.FullRowRank Q →
    ∀ R : AdmissibleBFGSRun n (fun x => objective (Q.mulVec x)), False) ∧
  (∀ {n : ℕ} (u v : Vec n), LinearIndependent ℝ ![u,v] →
    ∀ R : AdmissibleBFGSRun n (fun x => |dot u x|+dot v x), False)

theorem twoPieceLinearImage : TwoPieceLinearImageTarget :=
  ⟨@no_infinite_linear_image,@no_infinite_independent_two_piece⟩

end BfgsVerification.TwoPieceBudget
