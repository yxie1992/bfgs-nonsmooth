import BfgsVerification.SemialgebraicSmoothConcatenation
import BfgsVerification.SemialgebraicScalarGraphArithmetic

noncomputable section
open Set MvPolynomial
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

def SemialgebraicPiecewiseSmoothConnected (S : Set (σ → ℝ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, SemialgebraicPiecewiseSmoothPathIn S x y

theorem semialgebraicPiecewiseSmoothPathIn_equivalence (S : Set (σ → ℝ)) :
    Equivalence (fun x y : S => SemialgebraicPiecewiseSmoothPathIn S x.val y.val) :=
  ⟨fun x => SemialgebraicPiecewiseSmoothPathIn.refl x.property,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem SemialgebraicPiecewiseSmoothConnected.toPiecewiseSmoothConnected
    {S : Set (σ → ℝ)} (hS : SemialgebraicPiecewiseSmoothConnected S) :
    PiecewiseSmoothConnected S := fun _ hx _ hy => (hS _ hx _ hy).forget

theorem SemialgebraicPiecewiseSmoothConnected.convex {S : Set (σ → ℝ)}
    (hS : Convex ℝ S) : SemialgebraicPiecewiseSmoothConnected S :=
  fun _ hx _ hy => SemialgebraicPiecewiseSmoothPathIn.segment hS hx hy

theorem SemialgebraicPiecewiseSmoothConnected.image {S : Set (σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) {G : (σ → ℝ) → τ → ℝ}
    (hG : ContDiffOn ℝ ∞ G S) (hGsa : IsSemialgebraicMapOn G S) :
    SemialgebraicPiecewiseSmoothConnected (G '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (hS x hx y hy).map hG hGsa (fun z hz => ⟨z, hz, rfl⟩)

theorem option_graph_lift_contDiffOn {S : Set (σ → ℝ)} {f : (σ → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f S) :
    ContDiffOn ℝ ∞ (fun x j => Option.elim j (f x) x) S := by
  apply contDiffOn_pi.mpr
  intro i
  cases i with
  | none => exact hf
  | some i => exact (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff.contDiffOn

theorem SemialgebraicPiecewiseSmoothConnected.graph {S : Set (σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) (hSsa : IsSemialgebraic S)
    {f : (σ → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    (hfsa : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))}) :
    SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))} := by
  have h := hS.image (option_graph_lift_contDiffOn hf) (IsSemialgebraicMapOn.graph_lift hSsa hfsa)
  convert h using 1
  ext v
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨fun i => v (some i), hx, ?_⟩
    funext i
    cases i with
    | none => exact he.symm
    | some i => rfl
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩

/-- Every convex vertical fiber admits actual semialgebraic segment paths.
The target fiber itself is not assumed semialgebraic. -/
theorem semialgebraic_vertical_path {T : Set (Option σ → ℝ)} (x : σ → ℝ)
    (hT : Convex ℝ {t : ℝ | (fun j => Option.elim j t x) ∈ T})
    {t u : ℝ} (ht : (fun j => Option.elim j t x) ∈ T)
    (hu : (fun j => Option.elim j u x) ∈ T) :
    SemialgebraicPiecewiseSmoothPathIn T
      (fun j => Option.elim j t x) (fun j => Option.elim j u x) := by
  let A : Set (Fin 1 → ℝ) := {v | (fun j => Option.elim j (v 0) x) ∈ T}
  have hA : Convex ℝ A := by
    intro v hv w hw a b ha hb hab
    exact hT hv hw ha hb hab
  have hp := SemialgebraicPiecewiseSmoothPathIn.segment hA
    (show (fun _ : Fin 1 => t) ∈ A from ht) (show (fun _ : Fin 1 => u) ∈ A from hu)
  let G : (Fin 1 → ℝ) → Option σ → ℝ := fun v j => Option.elim j (v 0) x
  have hG : ContDiff ℝ ∞ G := by
    apply contDiff_pi.mpr
    intro j
    cases j with
    | none => exact (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).contDiff
    | some i => exact contDiff_const
  have hGsa : IsSemialgebraicMapOn G univ := by
    convert IsSemialgebraicMapOn.polynomial
      (fun j : Option σ => Option.elim j (X 0 : MvPolynomial (Fin 1) ℝ) (fun i => C (x i)))
      (isSemialgebraic_univ (σ := Fin 1)) using 1
    funext v j
    cases j <;> simp [G]
  exact hp.mapOn hG.contDiffOn hGsa (subset_univ _) (fun _ h => h)

end RealAlgebraicGeometry
end BfgsVerification
