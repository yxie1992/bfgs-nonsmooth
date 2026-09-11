import BfgsVerification.GeneralCoordinateProjection
import BfgsVerification.SemialgebraicGraphs

noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {σ τ υ : Type*} [Fintype σ] [Fintype τ] [Fintype υ]

/-- The actual graph of a coordinate map restricted to its given domain. -/
def IsSemialgebraicMapOn (G : (σ → ℝ) → τ → ℝ) (S : Set (σ → ℝ)) : Prop :=
  IsSemialgebraic {v : σ ⊕ τ → ℝ |
    (fun i => v (.inl i)) ∈ S ∧ (fun j => v (.inr j)) = G (fun i => v (.inl i))}

theorem IsSemialgebraicMapOn.polynomial (P : τ → MvPolynomial σ ℝ)
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraicMapOn (fun x j => MvPolynomial.eval x (P j)) S := by
  have hbase := hS.reindex (Sum.inl : σ → σ ⊕ τ)
  have heq := isSemialgebraic_forall_finite
    (fun j : τ => {v : σ ⊕ τ → ℝ | v (.inr j) = MvPolynomial.eval (fun i => v (.inl i)) (P j)})
    (fun j => by
      convert isSemialgebraic_equal_zero
        (X (.inr j) - rename Sum.inl (P j) : MvPolynomial (σ ⊕ τ) ℝ) using 1
      ext v
      simp only [mem_setOf_eq,MvPolynomial.eval_sub,MvPolynomial.eval_X,
        MvPolynomial.eval_rename,Function.comp_def,sub_eq_zero])
  unfold IsSemialgebraicMapOn
  convert hbase.inter heq using 1
  ext v
  simp only [mem_inter_iff,mem_setOf_eq,_root_.funext_iff]

theorem IsSemialgebraicMapOn.mono {G : (σ → ℝ) → τ → ℝ} {S T : Set (σ → ℝ)}
    (hG : IsSemialgebraicMapOn G S) (hT : IsSemialgebraic T) (hTS : T ⊆ S) :
    IsSemialgebraicMapOn G T := by
  have h := (hT.reindex (Sum.inl : σ → σ ⊕ τ)).inter hG
  unfold IsSemialgebraicMapOn
  convert h using 1
  ext v
  change (_ ∈ T ∧ _ = _) ↔ _ ∈ T ∧ _ ∈ S ∧ _ = _
  exact ⟨fun h => ⟨h.1,hTS h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩

theorem IsSemialgebraicMapOn.comp {G : (σ → ℝ) → τ → ℝ}
    {H : (τ → ℝ) → υ → ℝ} {S : Set (σ → ℝ)} {T : Set (τ → ℝ)}
    (hG : IsSemialgebraicMapOn G S) (hH : IsSemialgebraicMapOn H T)
    (hGT : MapsTo G S T) : IsSemialgebraicMapOn (H ∘ G) S := by
  let a : σ ⊕ τ → (σ ⊕ υ) ⊕ τ := Sum.elim (fun i => .inl (.inl i)) Sum.inr
  let b : τ ⊕ υ → (σ ⊕ υ) ⊕ τ := Sum.elim Sum.inr (fun j => .inl (.inr j))
  have h := coordinate_projection_semialgebraic ((hG.reindex a).inter (hH.reindex b))
  unfold IsSemialgebraicMapOn
  convert h using 1
  ext v
  change (_ ∈ S ∧ _ = _) ↔ ∃ y : τ → ℝ, _
  simp only [mem_inter_iff,mem_setOf_eq,a,b,Sum.elim_inl,Sum.elim_inr]
  constructor
  · rintro ⟨hx,hz⟩
    exact ⟨G (fun i => v (.inl i)),⟨hx,rfl⟩,hGT hx,hz⟩
  · rintro ⟨y,⟨hx,hy⟩,_,hz⟩
    change y = _ at hy
    subst y
    exact ⟨hx,hz⟩

theorem IsSemialgebraicMapOn.coordinatewise {G : (σ → ℝ) → τ → ℝ}
    {S : Set (σ → ℝ)} (hS : IsSemialgebraic S)
    (hG : ∀ j, IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = G (fun i => v (some i)) j}) :
    IsSemialgebraicMapOn G S := by
  have hbase := hS.reindex (Sum.inl : σ → σ ⊕ τ)
  have hj := isSemialgebraic_forall_finite
    (fun j : τ => {v : σ ⊕ τ → ℝ | (fun i => v (.inl i)) ∈ S ∧
      v (.inr j) = G (fun i => v (.inl i)) j})
    (fun j => (hG j).reindex (fun k => Option.elim k (.inr j) Sum.inl))
  unfold IsSemialgebraicMapOn
  convert hbase.inter hj using 1
  ext v
  change (_ ∈ S ∧ _ = _) ↔ _ ∈ S ∧ ∀ j, _ ∈ S ∧ _ = _
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨hx,fun j => ⟨hx,congrFun he j⟩⟩
  · rintro ⟨hx,he⟩
    exact ⟨hx,funext (fun j => (he j).2)⟩

end RealAlgebraicGeometry
end BfgsVerification
