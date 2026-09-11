import BfgsVerification.HomogeneousAffineObstruction

/-! The explicit many-piece common-tilt family from Module H.B. The first
coordinate is the scalar tilt coordinate; the remaining coordinates are u. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification
namespace Homogeneous

/-- Source family t + max_b b·u, in coordinates x=(t,u). -/
def commonTilt {n : ℕ} (B : Finset (Vec n)) (hB : B.Nonempty) (x : Vec (n + 1)) : ℝ :=
  x 0 + finiteMaxLinear B hB (Fin.tail x)

theorem dot_cons_one {n : ℕ} (b : Vec n) (x : Vec (n + 1)) :
    dot (Fin.cons 1 b) x = x 0 + dot b (Fin.tail x) := by
  unfold dot
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, one_mul, Fin.cons_succ, Fin.tail]

def tiltedSlope {n : ℕ} (b : Vec n) : Vec (n + 1) := Fin.cons 1 b

theorem commonTilt_eq_finiteMaxLinear {n : ℕ} (B : Finset (Vec n)) (hB : B.Nonempty) :
    commonTilt B hB = finiteMaxLinear (B.image (tiltedSlope (n := n)))
      (hB.image (tiltedSlope (n := n))) := by
  classical
  funext x
  apply le_antisymm
  · obtain ⟨b, hb, he⟩ := finiteMaxLinear_active B hB (Fin.tail x)
    change x 0 + finiteMaxLinear B hB (Fin.tail x) ≤ _
    rw [he, ← dot_cons_one]
    exact slope_le_finiteMaxLinear _ _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩) x
  · obtain ⟨a, ha, he⟩ := finiteMaxLinear_active
      (B.image (tiltedSlope (n := n))) (hB.image (tiltedSlope (n := n))) x
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    rw [he, tiltedSlope, dot_cons_one]
    exact add_le_add_left (slope_le_finiteMaxLinear B hB hb (Fin.tail x)) _

end Homogeneous

namespace AdmissibleBFGSRun

/-- Every infinite admissible run on t + max_b b·u drives values to minus
infinity, with arbitrary finite slope count and no finite-termination claim. -/
theorem commonTilt_value_escape {n : ℕ} (B : Finset (Vec n)) (hB : B.Nonempty)
    (R : AdmissibleBFGSRun (n + 1) (Homogeneous.commonTilt B hB)) :
    Tendsto (fun k => Homogeneous.commonTilt B hB (R.x k)) atTop atBot := by
  classical
  have heq := Homogeneous.commonTilt_eq_finiteMaxLinear B hB
  let A := B.image (Homogeneous.tiltedSlope (n := n))
  have hA : A.Nonempty := hB.image _
  change Homogeneous.commonTilt B hB = Homogeneous.finiteMaxLinear A hA at heq
  have hcommon : ∀ a ∈ A, dot (Pi.single 0 1) a = 1 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    change dotProduct (Pi.single 0 1) (Fin.cons 1 b) = 1
    rw [dotProduct_comm, dotProduct_single_one]
    rfl
  let Q : AdmissibleBFGSRun (n + 1) (Homogeneous.finiteMaxLinear A hA) := heq ▸ R
  have cast_x {F G : Vec (n + 1) → ℝ} (h : F = G)
      (P : AdmissibleBFGSRun (n + 1) F) :
      (h ▸ P : AdmissibleBFGSRun (n + 1) G).x = P.x := by
    cases h
    rfl
  have hx : Q.x = R.x := cast_x heq R
  have hescape := maxLinear_common_component_escape A hA Q (Pi.single 0 1) hcommon
  simpa only [hx, ← heq] using hescape

end AdmissibleBFGSRun
end BfgsVerification
