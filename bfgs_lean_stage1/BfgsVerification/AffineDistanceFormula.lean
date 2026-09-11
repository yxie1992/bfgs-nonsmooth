import BfgsVerification.AffineBarycentricLocal
import BfgsVerification.AffineCriticalObjective

/-! An explicit minimum-norm affine point from the actual augmented Gram matrix.
The formula handles every nonempty affinely independent family, including singletons. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification
namespace AffineDistance
open AffineBarycentric AffineCriticalGeometry AffineCriticalObjective

def inverseOnes {n m : ℕ} (g : Fin m → Vec n) : Vec m :=
  (gram (augmented g))⁻¹.mulVec (fun _ => 1)

def denominator {n m : ℕ} (g : Fin m → Vec n) : ℝ := ∑ i, inverseOnes g i

def weights {n m : ℕ} (g : Fin m → Vec n) : Vec m := (denominator g)⁻¹ • inverseOnes g

def formulaPoint {n m : ℕ} (g : Fin m → Vec n) : EuclideanSpace ℝ (Fin n) :=
  ∑ i, weights g i • euclideanVector (g i)

theorem denominator_pos {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hg : AffineIndependent ℝ g) : 0 < denominator g := by
  have hK := (gram_posDef (augmented g) ((affineIndependent_iff_augmented_injective g).mp hg)).inv
  have he : (fun _ : Fin m => (1 : ℝ)) ≠ 0 := by
    intro h; have hi := congrFun h i; norm_num at hi
  simpa [denominator, inverseOnes, dotProduct] using hK.2 _ he

theorem weights_sum {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hg : AffineIndependent ℝ g) : ∑ j, weights g j = 1 := by
  simp only [weights, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact inv_mul_cancel₀ (denominator_pos g i hg).ne'

theorem gram_weights {n m : ℕ} (g : Fin m → Vec n)
    (hg : AffineIndependent ℝ g) :
    (gram (augmented g)).mulVec (weights g) = (denominator g)⁻¹ • (fun _ : Fin m => (1 : ℝ)) := by
  have hK := gram_posDef (augmented g) ((affineIndependent_iff_augmented_injective g).mp hg)
  rw [weights, Matrix.mulVec_smul, inverseOnes, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hK.det_pos.ne'.isUnit, Matrix.one_mulVec]

theorem augmented_gram_pairing {n m : ℕ} (g : Fin m → Vec n) (w : Vec m) (i : Fin m) :
    (gram (augmented g)).mulVec w i = (∑ j, w j) +
      ⟪euclideanVector (g i), ∑ j, w j • euclideanVector (g j)⟫_ℝ := by
  rw [gram, ← Matrix.mulVec_mulVec]
  change dotProduct (fun k => augmented g k i) ((augmented g).mulVec w) = _
  rw [dotProduct, Fin.sum_univ_succ]
  simp only [augmented, Fin.cases_zero, Fin.cases_succ, one_mul]
  rw [augmented_mulVec_zero_row]
  congr 1
  simp only [augmented_mulVec_succ_row, inner_sum, real_inner_smul_right, euclidean_pairing_eq_dot,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dot, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem formulaPoint_mem_affineSpan {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hg : AffineIndependent ℝ g) :
    formulaPoint g ∈ affineSpan ℝ (range (fun j => euclideanVector (g j))) := by
  have h := affineCombination_mem_affineSpan (s := Finset.univ)
    (weights_sum g i hg) (fun j => euclideanVector (g j))
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ (weights_sum g i hg)] using h

theorem formulaPoint_pairing_constant {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hg : AffineIndependent ℝ g) (j : Fin m) :
    ⟪euclideanVector (g j), formulaPoint g⟫_ℝ = (denominator g)⁻¹ - 1 := by
  have h := congrFun (gram_weights g hg) j
  rw [augmented_gram_pairing, weights_sum g i hg] at h
  change 1 + ⟪euclideanVector (g j), formulaPoint g⟫_ℝ = (denominator g)⁻¹ * 1 at h
  linarith

theorem formulaPoint_eq_closest {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hg : AffineIndependent ℝ g) :
    formulaPoint g = closestAffinePoint (fun j => euclideanVector (g j)) i := by
  apply eq_closest_of_pairings _ i _ (formulaPoint_mem_affineSpan g i hg)
  have hn : ‖formulaPoint g‖^2 = (denominator g)⁻¹ - 1 := by
    have h := affine_pairing_of_constant (fun j => euclideanVector (g j)) (formulaPoint g)
      ((denominator g)⁻¹ - 1) (formulaPoint_pairing_constant g i hg)
      (formulaPoint g) (formulaPoint_mem_affineSpan g i hg)
    simpa only [real_inner_self_eq_norm_sq] using h
  intro j
  rw [hn]
  exact formulaPoint_pairing_constant g i hg j

theorem affine_distance_eq_formula {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hg : AffineIndependent ℝ g) :
    Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (affineSpan ℝ (range (fun j => euclideanVector (g j))) : Set _) =
      ‖formulaPoint g‖ := by
  rw [formulaPoint_eq_closest g i hg]
  exact infDist_affineSpan_eq_norm_closest _ i

end AffineDistance
end BfgsVerification
