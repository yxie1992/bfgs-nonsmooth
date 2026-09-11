import BfgsVerification.PolynomialFibers
import BfgsVerification.GeneralCoordinateProjection

/-! Finite parameter refinement by the actual polynomial signs on finitely many
actual boundary graphs. No smoothness, ordering or root-membership assumption
is needed for this definability and covering step. -/
noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- The signs of all the given polynomials on all the given boundary values. -/
def boundarySignStratum {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n))
    (ω : Fin m → Fin r → SignType) : Set (Vec n) :=
  {x | x ∈ S ∧ ∀ j i, SignType.sign (parameterEval (P j) (x, f i x)) = ω j i}

theorem restricted_graph_polynomial_sign_semialgebraic {n : ℕ}
    (p : MvPolynomial (Option (Fin n)) ℝ) {S : Set (Vec n)} {f : Vec n → ℝ}
    (hgraph : IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))}) (s : SignType) :
    IsSemialgebraic {x | x ∈ S ∧ SignType.sign (parameterEval p (x, f x)) = s} := by
  have h := (hgraph.inter ((finiteSemialgebraic_polynomial_sign p).fiber s)).scalar_projection
  convert h using 1
  ext x
  simp only [mem_setOf_eq, mem_inter_iff]
  have he : ∀ t, parameterPoint x t = (fun j : Option (Fin n) => j.elim t x) := by
    intro t
    funext j
    cases j <;> rfl
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨f x, ⟨hx, rfl⟩, ?_⟩
    simpa only [parameterEval, he] using hs
  · rintro ⟨t, ⟨hx, ht⟩, hs⟩
    change t = f x at ht
    subst t
    refine ⟨hx, ?_⟩
    simpa only [parameterEval, he] using hs

theorem boundarySignStratum_semialgebraic {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n))
    (hS : IsSemialgebraic S)
    (hgraph : ∀ i, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = f i (fun k => v (some k))})
    (ω : Fin m → Fin r → SignType) : IsSemialgebraic (boundarySignStratum P f S ω) := by
  have h := hS.inter (isSemialgebraic_forall_finite
    (fun j : Fin m => {x | ∀ i : Fin r, x ∈ S ∧
      SignType.sign (parameterEval (P j) (x, f i x)) = ω j i})
    (fun j => isSemialgebraic_forall_finite
      (fun i : Fin r => {x | x ∈ S ∧
        SignType.sign (parameterEval (P j) (x, f i x)) = ω j i})
      (fun i => restricted_graph_polynomial_sign_semialgebraic (P j) (hgraph i) (ω j i))))
  convert h using 1
  ext x
  simp only [boundarySignStratum, mem_setOf_eq, mem_inter_iff]
  constructor
  · rintro ⟨hx, hs⟩
    exact ⟨hx, fun j i => ⟨hx, hs j i⟩⟩
  · rintro ⟨hx, hs⟩
    exact ⟨hx, fun j i => (hs j i).2⟩

theorem boundarySignStratum_cover {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n)) :
    (⋃ ω : Fin m → Fin r → SignType, boundarySignStratum P f S ω) = S := by
  ext x
  simp only [mem_iUnion, boundarySignStratum, mem_setOf_eq]
  constructor
  · rintro ⟨ω, hx, _⟩
    exact hx
  · intro hx
    exact ⟨fun j i => SignType.sign (parameterEval (P j) (x, f i x)), hx, fun _ _ => rfl⟩

theorem boundarySignStratum_pairwise_disjoint {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n)) :
    Pairwise (fun ω η => Disjoint (boundarySignStratum P f S ω)
      (boundarySignStratum P f S η)) := by
  intro ω η hne
  apply Set.disjoint_left.mpr
  intro x hx hη
  apply hne
  funext j i
  exact (hx.2 j i).symm.trans (hη.2 j i)

theorem boundarySignStratum_graph_sign {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n))
    (ω : Fin m → Fin r → SignType) (j : Fin m) (i : Fin r)
    {z : Vec n × ℝ} (hz : z.1 ∈ boundarySignStratum P f S ω ∧ z.2 = f i z.1) :
    SignType.sign (parameterEval (P j) z) = ω j i := by
  rcases z with ⟨x,t⟩
  rcases hz with ⟨hx, ht⟩
  dsimp at ht
  subst t
  exact hx.2 j i

theorem boundarySignStratum_restricted_graph_semialgebraic {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n))
    (hS : IsSemialgebraic S)
    (hgraph : ∀ i, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = f i (fun k => v (some k))})
    (ω : Fin m → Fin r → SignType) (i : Fin r) :
    IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ boundarySignStratum P f S ω ∧
        v none = f i (fun k => v (some k))} := by
  have h := (hgraph i).inter
    ((boundarySignStratum_semialgebraic P f S hS hgraph ω).reindex some)
  convert h using 1
  ext v
  simp only [mem_setOf_eq, mem_inter_iff]
  constructor
  · rintro ⟨hx, ht⟩
    exact ⟨⟨hx.1, ht⟩, hx⟩
  · rintro ⟨⟨_, ht⟩, hx⟩
    exact ⟨hx, ht⟩

end RealAlgebraicGeometry
end BfgsVerification
