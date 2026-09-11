import BfgsVerification.BoundarySignStrata

noncomputable section
open Set
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem boundary_sign_semialgebraic_partition {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n))
    (hS : IsSemialgebraic S)
    (hgraph : ∀ i, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = f i (fun k => v (some k))}) :
    (∀ ω, IsSemialgebraic (boundarySignStratum P f S ω)) ∧
    (⋃ ω : Fin m → Fin r → SignType, boundarySignStratum P f S ω) = S ∧
    Pairwise (fun ω η => Disjoint (boundarySignStratum P f S ω)
      (boundarySignStratum P f S η)) ∧
    (∀ ω i, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ boundarySignStratum P f S ω ∧
        v none = f i (fun k => v (some k))}) ∧
    ∀ ω j i (z : Vec n × ℝ),
      z.1 ∈ boundarySignStratum P f S ω ∧ z.2 = f i z.1 →
      SignType.sign (parameterEval (P j) z) = ω j i :=
  ⟨boundarySignStratum_semialgebraic P f S hS hgraph,
    boundarySignStratum_cover P f S,
    boundarySignStratum_pairwise_disjoint P f S,
    boundarySignStratum_restricted_graph_semialgebraic P f S hS hgraph,
    fun ω j i _ hz => boundarySignStratum_graph_sign P f S ω j i hz⟩

end RealAlgebraicGeometry
open RealAlgebraicGeometry

def BoundarySignPartitionTarget : Prop := ∀ {n m r : ℕ}
    (P : Fin m → MvPolynomial (Option (Fin n)) ℝ)
    (f : Fin r → Vec n → ℝ) (S : Set (Vec n)),
    IsSemialgebraic S →
    (∀ i, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ S ∧ v none = f i (fun k => v (some k))}) →
    (∀ ω, IsSemialgebraic (boundarySignStratum P f S ω)) ∧
    (⋃ ω : Fin m → Fin r → SignType, boundarySignStratum P f S ω) = S ∧
    Pairwise (fun ω η => Disjoint (boundarySignStratum P f S ω)
      (boundarySignStratum P f S η)) ∧
    (∀ ω i, IsSemialgebraic {v : Option (Fin n) → ℝ |
      (fun k => v (some k)) ∈ boundarySignStratum P f S ω ∧
        v none = f i (fun k => v (some k))}) ∧
    ∀ ω j i (z : Vec n × ℝ),
      z.1 ∈ boundarySignStratum P f S ω ∧ z.2 = f i z.1 →
      SignType.sign (parameterEval (P j) z) = ω j i

theorem boundarySignPartition : BoundarySignPartitionTarget :=
  boundary_sign_semialgebraic_partition

end BfgsVerification
