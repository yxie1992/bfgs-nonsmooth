import BfgsVerification.RationalIndexTargets
import BfgsVerification.PositivePseudoSpecialization

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem localCauchyIndex_const_mul_pos (f : ℝ → ℝ) (a : ℝ) {c : ℝ} (hc : 0<c) :
    localCauchyIndex (fun x => c*f x) a=localCauchyIndex f a := by
  classical
  have h1 := and_congr
    (tendsto_const_mul_atBot_of_pos (f := f) (l := 𝓝[<] a) hc)
    (tendsto_const_mul_atTop_of_pos (f := f) (l := 𝓝[>] a) hc)
  have h2 := and_congr
    (tendsto_const_mul_atTop_of_pos (f := f) (l := 𝓝[<] a) hc)
    (tendsto_const_mul_atBot_of_pos (f := f) (l := 𝓝[>] a) hc)
  exact if_congr h1 rfl (if_congr h2 rfl rfl)

theorem rationalCauchyIndex_C_mul_pos (p q : Polynomial ℝ) {c : ℝ} (hc : 0<c) :
    rationalCauchyIndex (C c*p) q=rationalCauchyIndex p q := by
  classical
  unfold rationalCauchyIndex
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun x => (C c*p).eval x/q.eval x) =
      (fun x => c*(p.eval x/q.eval x)) := by
    funext x
    simp only [eval_mul, eval_C]
    ring
  rw [he]
  exact localCauchyIndex_const_mul_pos _ _ hc

theorem positive_pseudo_index_eq {p q Q r : Polynomial ℝ} {c : ℝ}
    (hc : 0<c) (he : C c*p=q*Q+r) (hq : q≠0) :
    rationalCauchyIndex p q=rationalCauchyIndex r q := by
  calc
    _ = rationalCauchyIndex (C c*p) q := (rationalCauchyIndex_C_mul_pos p q hc).symm
    _ = rationalCauchyIndex (r+q*Q) q := by rw [he, add_comm]
    _ = _ := rationalCauchyIndex_add_mul r Q hq

theorem positive_pseudo_index_zero {p q Q r : Polynomial ℝ} {c : ℝ}
    (hc : 0<c) (he : C c*p=q*Q+r) (hq : q≠0) (hr : r=0) :
    rationalCauchyIndex p q=0 := by
  rw [positive_pseudo_index_eq hc he hq, hr, rationalCauchyIndex_zero_numerator]

theorem positive_pseudo_index_recurrence {p q Q r : Polynomial ℝ} {c : ℝ}
    (hc : 0<c) (he : C c*p=q*Q+r) (hq : q≠0) (hr : r≠0) :
    rationalCauchyIndex p q=infinityVariation r q-rationalCauchyIndex q r := by
  have heq := positive_pseudo_index_eq hc he hq
  have hrec := rationalCauchyIndex_reciprocity hr hq
  omega

theorem infinityVariation_eq_odd (p q : Polynomial ℝ) :
    infinityVariation p q =
      if Odd (p*q).natDegree then (SignType.sign (p*q).leadingCoeff : ℤ) else 0 := by
  unfold infinityVariation
  by_cases ho : Odd (p*q).natDegree
  · rw [if_pos ho, ho.neg_one_pow]
    omega
  · rw [if_neg ho, (Nat.not_odd_iff_even.mp ho).neg_one_pow]
    simp

theorem infinityVariation_mem_three (p q : Polynomial ℝ) :
    infinityVariation p q ∈ ({-1,0,1} : Finset ℤ) := by
  rw [infinityVariation_eq_odd]
  split_ifs
  · cases SignType.sign (p*q).leadingCoeff <;> decide
  · decide

end RealAlgebraicGeometry
end BfgsVerification
