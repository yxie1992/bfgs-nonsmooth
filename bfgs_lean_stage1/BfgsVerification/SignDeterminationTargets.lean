import BfgsVerification.RootSignDetermination

noncomputable section
open scoped BigOperators
open Polynomial
namespace BfgsVerification
open RealAlgebraicGeometry

/-- Exact finite-query reconstruction of all simultaneous sign counts. -/
def RootSignReconstructionTarget : Prop := ∀ {m : ℕ} (p : Polynomial ℝ)
    (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType),
    (rootSignCount p q σ : ℚ)=∑e : Fin m → Fin 3,
      signPatternCoeff σ e * (tarskiQuery p (signQueryPolynomial q e) : ℚ)

theorem rootSignReconstruction : RootSignReconstructionTarget := root_sign_count_from_tarskiQueries

/-- A single common actual root realizes the complete pattern exactly when
the explicit rational query expression is positive. -/
def SimultaneousRootSignsTarget : Prop := ∀ {m : ℕ} {p : Polynomial ℝ},p≠0 →
    ∀ (q : Fin m → Polynomial ℝ) (σ : Fin m → SignType),
    (∃a : ℝ,p.eval a=0 ∧ ∀i,SignType.sign ((q i).eval a)=σ i) ↔
      0<∑e : Fin m → Fin 3,signPatternCoeff σ e * (tarskiQuery p (signQueryPolynomial q e) : ℚ)

theorem simultaneousRootSigns : SimultaneousRootSignsTarget := exists_root_sign_pattern_iff_query_positive

/-- The finite query vector determines every sign count, without requiring
that root degrees or multiplicities agree between the two fibers. -/
def SignQueryDeterminationTarget : Prop := ∀ {m : ℕ} (p p' : Polynomial ℝ)
    (q q' : Fin m → Polynomial ℝ),
    (∀e,tarskiQuery p (signQueryPolynomial q e)=tarskiQuery p' (signQueryPolynomial q' e)) →
      ∀σ,rootSignCount p q σ=rootSignCount p' q' σ

theorem signQueryDetermination : SignQueryDeterminationTarget := root_sign_counts_eq_of_queries_eq

end BfgsVerification
