import BfgsVerification.AffinePathConstancy

/-! The real-order final step in A:semialgebraic, under an explicitly stated
finite-value premise. This does not prove that premise for semialgebraic data. -/
noncomputable section
open scoped Topology
open Set Filter

namespace BfgsVerification
namespace AffineSupportPath
open AffineCriticalObjective ConvexSubdifferential

/-- A finite subset of the real line has a positive gap above any given value,
whether or not the subset contains a larger value. -/
theorem finite_set_gap_above {S : Set ℝ} (hS : S.Finite) (v : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ S, v < a → v + ε ≤ a := by
  classical
  have ho : IsOpen (S \ {v})ᶜ := (hS.diff (t := {v})).isClosed.isOpen_compl
  have hv : v ∈ (S \ {v})ᶜ := by simp
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hv)
  refine ⟨ε,hε,?_⟩
  intro a ha hva
  by_contra hn
  have hlt : a < v + ε := lt_of_not_ge hn
  have haball : a ∈ Metric.ball v ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hva)]
    linarith
  exact hball haball ⟨ha,by simpa only [mem_singleton_iff] using hva.ne'⟩

/-- Finite actual affine-critical values imply the source's low-level
stationarity conclusion. Finiteness is an explicit conditional premise here;
no semialgebraic projection or decomposition result is assumed implicitly. -/
theorem low_level_affine_correct_of_finite_values {n : ℕ} {F : Vec n → ℝ}
    (hfinite : (F '' {p | IsAffineCritical F p}).Finite)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p, F p < F star + ε →
      IsAffineCritical F p → (0 : Vec n) ∈ subdifferential F p := by
  obtain ⟨ε,hε,hgap⟩ := finite_set_gap_above hfinite (F star)
  refine ⟨ε,hε,?_⟩
  intro p hp hac
  have hle : F p ≤ F star := by
    by_contra hn
    exact (not_lt_of_ge (hgap (F p) ⟨p,hac,rfl⟩ (lt_of_not_ge hn))) hp
  apply zero_mem_iff_global_minimum.mpr
  intro z
  exact hle.trans (hmin z)

end AffineSupportPath
end BfgsVerification
