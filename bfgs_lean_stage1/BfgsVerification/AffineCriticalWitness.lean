import BfgsVerification.SemialgebraicSupportProjection
import BfgsVerification.AffineBoundedRepresentation

noncomputable section
open scoped BigOperators
open Set MvPolynomial
namespace BfgsVerification.RealAlgebraicGeometry
open AffineSupportPath AffineCriticalObjective

abbrev AffineAux (n m : ℕ) := (Fin m × Fin n) ⊕ Fin m
abbrev AffineAll (n m : ℕ) := Fin n ⊕ AffineAux n m

def affineWitnessSet {n : ℕ} (F : Vec n → ℝ) (m : ℕ) : Set (AffineAll n m → ℝ) :=
  {v | (∀ i : Fin m, Homogeneous.Supports F (fun j => v (.inl j))
      (fun j => v (.inr (.inl (i,j))))) ∧
    (∑ i : Fin m, v (.inr (.inr i))) = 1 ∧
    ∀ j : Fin n, (∑ i : Fin m, v (.inr (.inr i)) * v (.inr (.inl (i,j)))) = 0}

theorem affineWitnessSet_semialgebraic {n : ℕ} {F : Vec n → ℝ}
    (hF : IsSemialgebraic (supportGraph F)) (m : ℕ) :
    IsSemialgebraic (affineWitnessSet F m) := by
  classical
  let S : Fin m → Set (AffineAll n m → ℝ) := fun i =>
    {v | Homogeneous.Supports F (fun j => v (.inl j))
      (fun j => v (.inr (.inl (i,j))))}
  have hS : ∀ i, IsSemialgebraic (S i) := by
    intro i
    have h := hF.polynomial_preimage (fun k : SupportBase n =>
      (X (match k with
        | .inl j => .inl j
        | .inr j => .inr (.inl (i,j))) : MvPolynomial (AffineAll n m) ℝ))
    convert h using 1
    ext v
    simp only [S, supportGraph, mem_setOf_eq, mem_preimage, MvPolynomial.eval_X]
  have hsum : IsSemialgebraic {v : AffineAll n m → ℝ |
      (∑ i : Fin m, v (.inr (.inr i))) = 1} := by
    have h := isSemialgebraic_equal_zero
      ((∑ i : Fin m, X (.inr (.inr i))) - 1 : MvPolynomial (AffineAll n m) ℝ)
    convert h using 1
    ext v
    simp only [mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_sum,
      MvPolynomial.eval_X, map_one, sub_eq_zero]
  let Z : Fin n → Set (AffineAll n m → ℝ) := fun j =>
    {v | (∑ i : Fin m, v (.inr (.inr i)) * v (.inr (.inl (i,j)))) = 0}
  have hZ : ∀ j, IsSemialgebraic (Z j) := by
    intro j
    have h := isSemialgebraic_equal_zero
      (∑ i : Fin m, X (.inr (.inr i)) * X (.inr (.inl (i,j))) : MvPolynomial (AffineAll n m) ℝ)
    convert h using 1
    ext v
    simp only [Z, mem_setOf_eq, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
  have h := (isSemialgebraic_finset_inter Finset.univ S (fun i _ => hS i)).inter
    (hsum.inter (isSemialgebraic_finset_inter Finset.univ Z (fun j _ => hZ j)))
  convert h using 1
  ext v
  simp only [affineWitnessSet, S, Z, mem_setOf_eq, mem_inter_iff, mem_iInter,
    Finset.mem_univ, forall_const]

theorem affineWitness_projection_iff {n m : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    x ∈ coordinateProjection (affineWitnessSet F m) ↔
      ∃ g : Fin m → Vec n, ∃ w : Fin m → ℝ,
        (∀ i, Homogeneous.Supports F x (g i)) ∧
        (∑ i, w i) = 1 ∧ (∑ i, w i • g i) = 0 := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨(fun i j => v (.inl (i,j))), (fun i => v (.inr i)), hv.1, hv.2.1, ?_⟩
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using hv.2.2 j
  · rintro ⟨g,w,hg,hw,hz⟩
    refine ⟨Sum.elim (fun ij => g ij.1 ij.2) w, hg, hw, ?_⟩
    intro j
    have h := congrFun hz j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using h

/-- The actual affine-critical set has this finite projection representation.
The witness sets use actual supporting vectors and signed affine coefficients. -/
theorem affineCritical_set_eq_finite_projection_union {n : ℕ} (F : Vec n → ℝ) :
    {x | IsAffineCritical F x} =
      ⋃ m : Fin (n+2), coordinateProjection (affineWitnessSet F m.val) := by
  ext x
  simp only [mem_setOf_eq, mem_iUnion, affineWitness_projection_iff]
  rw [isAffineCritical_iff_bounded_supports]
  constructor
  · rintro ⟨m,hm,hmb,g,w,hg,hw,hz⟩
    exact ⟨⟨m,by omega⟩,g,w,hg,hw,hz⟩
  · rintro ⟨m,g,w,hg,hw,hz⟩
    have hm : 0 < m.val := by
      by_contra hn
      have hzero : m.val=0 := by omega
      have : IsEmpty (Fin m.val) := by rw [hzero]; infer_instance
      letI := this
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hw
      norm_num at hw
    exact ⟨m.val,hm,by omega,g,w,hg,hw,hz⟩

end BfgsVerification.RealAlgebraicGeometry
