import BfgsVerification.SemialgebraicPathFiniteCovers

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem semialgebraicPiecewiseSmoothConnected_reindex {S : Set (σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) (hSA : IsSemialgebraic S) (e : σ ≃ τ) :
    SemialgebraicPiecewiseSmoothConnected {y : τ → ℝ | (fun i => y (e i)) ∈ S} := by
  let G : (σ → ℝ) → (τ → ℝ) := fun x j => x (e.symm j)
  have hg : ContDiff ℝ ∞ G := by
    apply contDiff_pi.mpr
    intro j
    exact (ContinuousLinearMap.proj (e.symm j) : (σ → ℝ) →L[ℝ] ℝ).contDiff
  have hGsa : IsSemialgebraicMapOn G S := by
    simpa only [MvPolynomial.eval_X] using
      IsSemialgebraicMapOn.polynomial (fun j => MvPolynomial.X (e.symm j)) hSA
  have h := hS.image hg.contDiffOn hGsa
  convert h using 1
  ext y
  constructor
  · intro hy
    refine ⟨fun i => y (e i),hy,?_⟩
    ext j
    exact congrArg y (e.apply_symm_apply j)
  · rintro ⟨x,hx,rfl⟩
    simpa only [mem_setOf_eq,G,e.symm_apply_apply] using hx

theorem HasFiniteSemialgebraicPathCover.reindex {S : Set (σ → ℝ)}
    (hS : HasFiniteSemialgebraicPathCover S) (e : σ ≃ τ) :
    HasFiniteSemialgebraicPathCover {y : τ → ℝ | (fun i => y (e i)) ∈ S} := by
  classical
  obtain ⟨C,hC,hcover⟩ := hS
  have h := HasFiniteSemialgebraicPathCover.iUnion (fun T : C =>
    HasFiniteSemialgebraicPathCover.of_connected ((hC T T.2).1.reindex e)
      (semialgebraicPiecewiseSmoothConnected_reindex (hC T T.2).2 (hC T T.2).1 e))
  convert h using 1
  ext y
  constructor
  · intro hy
    change (fun i => y (e i)) ∈ S at hy
    rw [← hcover] at hy
    obtain ⟨T,hTy⟩ := mem_iUnion.mp hy
    obtain ⟨hT,hyT⟩ := mem_iUnion.mp hTy
    exact mem_iUnion.mpr ⟨⟨T,hT⟩,hyT⟩
  · intro hy
    obtain ⟨T,hyT⟩ := mem_iUnion.mp hy
    change (fun i => y (e i)) ∈ S
    rw [← hcover]
    exact mem_iUnion.mpr ⟨T,mem_iUnion.mpr ⟨T.2,hyT⟩⟩

end RealAlgebraicGeometry
end BfgsVerification
