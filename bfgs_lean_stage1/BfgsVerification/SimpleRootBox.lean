import BfgsVerification.SimpleRootInverse

/-! A uniform product neighborhood for the proved scalar implicit root.
Both radii are chosen before all nearby parameters and scalar candidates. -/
noncomputable section
open scoped Topology ContDiff
open Set Filter
namespace BfgsVerification
namespace RealAlgebraicGeometry

/-- A simple root continues smoothly on one actual parameter ball and is the
unique root throughout one fixed scalar interval for all parameters in that ball. -/
theorem exists_smooth_root_box {n : ℕ} {F : Vec n × ℝ → ℝ} {a : Vec n} {b : ℝ}
    (hF : ContDiffAt ℝ ω F (a,b)) (hzero : F (a,b) = 0)
    (hD : fderiv ℝ F (a,b) (0,1) ≠ 0) :
    ∃ g : Vec n → ℝ, ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ g a = b ∧
      ContDiffOn ℝ ∞ g (Metric.ball a r) ∧
      ∀ x ∈ Metric.ball a r, dist (g x) b < δ ∧
        ∀ t : ℝ, dist t b < δ → (F (x,t) = 0 ↔ t = g x) := by
  obtain ⟨g,hg0,hgc,hroot,huniq⟩ := exists_smooth_root_germ (by simp) hF hzero hD
  obtain ⟨U,hU,hgU⟩ := hgc.contDiffOn (m := ∞) (by simp) (by intro _; rfl)
  obtain ⟨δ,hδ,hδuniq⟩ := Metric.mem_nhds_iff.mp huniq
  have hgt : Tendsto g (𝓝 a) (𝓝 b) := by simpa only [hg0] using hgc.continuousAt.tendsto
  have hgb := hgt (Metric.ball_mem_nhds b hδ)
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hU (inter_mem hroot (inter_mem hgb (Metric.ball_mem_nhds a hδ))))
  refine ⟨g,r,δ,hr,hδ,hg0,hgU.mono (fun x hx => (hrall hx).1),?_⟩
  intro x hx
  have hxall := hrall hx
  refine ⟨hxall.2.2.1,?_⟩
  intro t ht
  have hxt : (x,t) ∈ Metric.ball (a,b) δ := by
    simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hxall.2.2.2 ht
  constructor
  · intro hz
    exact hδuniq hxt hz
  · intro he
    rw [he]
    exact hxall.2.1

end RealAlgebraicGeometry
end BfgsVerification
