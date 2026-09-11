import BfgsVerification.FiniteSmoothCovers

noncomputable section
open Filter Set Polynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem piecewiseSmoothConnected_reindex {S : Set (σ → ℝ)}
    (hS : PiecewiseSmoothConnected S) (e : σ ≃ τ) :
    PiecewiseSmoothConnected {y : τ → ℝ | (fun i => y (e i)) ∈ S} := by
  let G : (σ → ℝ) → (τ → ℝ) := fun x j => x (e.symm j)
  have hg : ContDiff ℝ ∞ G := by
    apply contDiff_pi.mpr
    intro j
    exact (ContinuousLinearMap.proj (e.symm j) : (σ → ℝ) →L[ℝ] ℝ).contDiff
  have h := hS.image hg.contDiffOn
  convert h using 1
  ext y
  constructor
  · intro hy
    refine ⟨fun i => y (e i),hy,?_⟩
    ext j
    exact congrArg y (e.apply_symm_apply j)
  · rintro ⟨x,hx,rfl⟩
    simpa only [mem_setOf_eq,G,e.symm_apply_apply] using hx

theorem HasFiniteSmoothSemialgebraicCover.reindex {S : Set (σ → ℝ)}
    (hS : HasFiniteSmoothSemialgebraicCover S) (e : σ ≃ τ) :
    HasFiniteSmoothSemialgebraicCover {y : τ → ℝ | (fun i => y (e i)) ∈ S} := by
  classical
  obtain ⟨C,hC,hcover⟩ := hS
  have h := HasFiniteSmoothSemialgebraicCover.iUnion (fun T : C =>
    HasFiniteSmoothSemialgebraicCover.of_connected ((hC T T.2).1.reindex e)
      (piecewiseSmoothConnected_reindex (hC T T.2).2 e))
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
