import BfgsVerification.AlgebraicSeedOrbitGeometry
import BfgsVerification.BFGSScaling
noncomputable section
open scoped BigOperators Topology
open Matrix Filter
namespace BfgsVerification.SeedOrbit
open AlgebraicSeed SeedCycle

theorem StrictActive.scale {c d : ℝ} {x : Vec 2} {i : Fin 3} (hi : StrictActive c d x i)
    {t : ℝ} (ht : 0 < t) : StrictActive c d (t • x) i := by
  intro j hj
  simp only [dot_smul_right]
  exact mul_lt_mul_of_pos_left (hi j hj) ht

theorem PointCertificate.scale {c d : ℝ} {x : Vec 2} {i : Fin 3} (hi : PointCertificate c d x i)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : PointCertificate c d (t • x) i := by
  refine ⟨hi.active.scale ht,?_,?_,?_⟩
  · intro k
    rw [dot_smul_right,abs_mul,abs_of_pos ht]
    calc
      t*|dot (gradient c d k) x| < t*3 := mul_lt_mul_of_pos_left (hi.branch_bounds k) ht
      _ ≤ 3 := by linarith
  · change t*x 1 < 2
    nlinarith [mul_lt_mul_of_pos_left hi.vertical ht]
  · rw [dot_smul_right]
    exact mul_pos ht hi.value_pos

theorem objective_scale_at_active {c d : ℝ} {x : Vec 2} {i : Fin 3} (hi : StrictActive c d x i)
    {t : ℝ} (ht : 0 < t) : objective c d (t • x)=t*objective c d x := by
  rw [objective_of_active (hi.scale ht),objective_of_active hi,dot_smul_right]

theorem TrialCertificate.actual_accept {c d r : ℝ} {j i : Fin 3} {a c₁ c₂ : ℝ}
    (hbase : StrictActive c d (point c d r j) j)
    (h : TrialCertificate c d r j a i true)
    (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    objective c d (trial c d r j a) < objective c d (point c d r j)+
      c₁*dot (gradient c d j) (a • direction c d r j) ∧
    c₂*dot (gradient c d j) (a • direction c d r j) <
      dot (gradient c d i) (a • direction c d r j) := by
  rw [objective_of_active h.active,objective_of_active hbase]
  have ha := h.decision
  have hw := h.wolfe rfl
  simp only [Bool.true_eq,ite_true] at ha
  have hneg := h.descent
  constructor
  · exact ha.trans_le (add_le_add_left (mul_le_mul_of_nonpos_right hc₁' hneg.le) _)
  · exact (mul_neg_of_pos_of_neg hc₂ hneg).trans hw

theorem TrialCertificate.actual_reject {c d r : ℝ} {j i : Fin 3} {a c₁ : ℝ}
    (hbase : StrictActive c d (point c d r j) j)
    (h : TrialCertificate c d r j a i false) (hc₁ : 0 < c₁) :
    objective c d (point c d r j)+c₁*dot (gradient c d j) (a • direction c d r j) <
      objective c d (trial c d r j a) := by
  rw [objective_of_active h.active,objective_of_active hbase]
  have ha := h.decision
  simp only [Bool.false_eq_true,ite_false] at ha
  have hn := mul_neg_of_pos_of_neg hc₁ h.descent
  linarith

def phase (k : ℕ) : Fin 3 := ⟨k%3,Nat.mod_lt k (by decide)⟩
def period (k : ℕ) : ℕ := k/3

theorem phase_period_cases (k : ℕ) :
    (phase k=0 ∧ phase (k+1)=1 ∧ period (k+1)=period k) ∨
    (phase k=1 ∧ phase (k+1)=2 ∧ period (k+1)=period k) ∨
    (phase k=2 ∧ phase (k+1)=0 ∧ period (k+1)=period k+1) := by
  have hm := Nat.mod_lt k (by decide : 0 < 3)
  have hcases : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
  rcases hcases with h | h | h
  · left
    refine ⟨Fin.ext h,Fin.ext ?_,?_⟩
    · change (k+1)%3=1
      omega
    · dsimp [period]; omega
  · right; left
    refine ⟨Fin.ext h,Fin.ext ?_,?_⟩
    · change (k+1)%3=2
      omega
    · dsimp [period]; omega
  · right; right
    refine ⟨Fin.ext h,Fin.ext ?_,?_⟩
    · change (k+1)%3=0
      omega
    · dsimp [period]; omega

end BfgsVerification.SeedOrbit
