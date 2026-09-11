import BfgsVerification.ConvexDifferentiability
import BfgsVerification.Homogeneous
import Mathlib.Analysis.Convex.Topology

/-! The actual global supporting-vector set of a finite convex function.
Nonemptiness is derived from differentiability almost everywhere and compactness;
no differentiability or regularity of a selected subgradient is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace BfgsVerification
namespace ConvexSubdifferential

/-- The convex subdifferential, using the existing global supporting predicate. -/
def subdifferential {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Set (Vec n) :=
  {g | Homogeneous.Supports F x g}

@[simp] theorem mem_subdifferential {n : ℕ} {F : Vec n → ℝ} {x g : Vec n} :
    g ∈ subdifferential F x ↔ ∀ z, dot g (z - x) ≤ F z - F x := Iff.rfl

theorem isClosed_subdifferential {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    IsClosed (subdifferential F x) := by
  change IsClosed {g : Vec n | ∀ z, dot g (z - x) ≤ F z - F x}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro z
  apply isClosed_le _ continuous_const
  exact continuous_dot.comp (continuous_id.prodMk continuous_const)

theorem convex_subdifferential {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    Convex ℝ (subdifferential F x) := by
  intro a ha b hb s t hs ht hst z
  change (s • a + t • b) ⬝ᵥ (z - x) ≤ _
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
  change s * dot a (z - x) + t * dot b (z - x) ≤ _
  calc
    _ ≤ s * (F z - F x) + t * (F z - F x) :=
      add_le_add (mul_le_mul_of_nonneg_left (ha z) hs)
        (mul_le_mul_of_nonneg_left (hb z) ht)
    _ = F z - F x := by rw [← add_mul, hst, one_mul]

/-- Coordinate and Euclidean norm compatibility for the ambient Pi norm. -/
theorem norm_le_of_sqNorm_le {n : ℕ} {g : Vec n} {G : ℝ}
    (hG : 0 ≤ G) (hg : sqNorm g ≤ G ^ 2) : ‖g‖ ≤ G := by
  apply (pi_norm_le_iff_of_nonneg hG).2
  intro i
  have hi : (g i) ^ 2 ≤ sqNorm g :=
    Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) hG).mp
  simpa only [sq_abs] using hi.trans hg

/-- Every point of a finite convex objective has an actual global support. -/
theorem subdifferential_nonempty {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (x : Vec n) : (subdifferential F x).Nonempty := by
  have hdense : Dense {z : Vec n | DifferentiableAt ℝ F z} :=
    MeasureTheory.Measure.dense_of_ae (μ := volume) (convex_ae_differentiable hF)
  obtain ⟨z, hz, hzx⟩ := mem_closure_iff_seq_limit.mp (hdense x)
  let g : ℕ → Vec n := fun k => coordinateGradient F (z k)
  have hs (k : ℕ) (y : Vec n) : dot (g k) (y - z k) ≤ F y - F (z k) :=
    convex_supporting_inequality hF (hasFDerivAt_coordinateGradient (hz k)) y
  obtain ⟨G, hG, hbound⟩ :=
    convex_supporting_bound_on_compact hF hzx.isCompact_insert_range
  have hgball (k : ℕ) : g k ∈ Metric.closedBall (0 : Vec n) G := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_of_sqNorm_le hG.le
      (hbound (z k) (mem_insert_of_mem _ (mem_range_self k)) (g k) (hs k))
  obtain ⟨p, _, φ, hφ, hpconv⟩ :=
    (isCompact_closedBall (0 : Vec n) G).tendsto_subseq hgball
  exact ⟨p, supporting_limit (convex_continuous hF) (hzx.comp hφ.tendsto_atTop)
    hpconv (fun k y => hs (φ k) y)⟩

/-- Subdifferentials are compact, including at nondifferentiable points. -/
theorem isCompact_subdifferential {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (x : Vec n) : IsCompact (subdifferential F x) := by
  obtain ⟨G, hG, hbound⟩ :=
    convex_supporting_bound_on_compact hF (isCompact_singleton (x := x))
  apply (isCompact_closedBall (0 : Vec n) G).of_isClosed_subset
    (isClosed_subdifferential F x)
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_sqNorm_le hG.le (hbound x (mem_singleton x) g hg)

/-- The supporting graph is closed for every continuous objective. -/
theorem isClosed_graph {n : ℕ} {F : Vec n → ℝ} (hF : Continuous F) :
    IsClosed {p : Vec n × Vec n | p.2 ∈ subdifferential F p.1} := by
  change IsClosed {p : Vec n × Vec n | ∀ z, dot p.2 (z - p.1) ≤ F z - F p.1}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro z
  apply isClosed_le
  · exact continuous_dot.comp
      (continuous_snd.prodMk (continuous_const.sub continuous_fst))
  · exact continuous_const.sub (hF.comp continuous_fst)

@[simp] theorem zero_mem_iff_global_minimum {n : ℕ} {F : Vec n → ℝ} {x : Vec n} :
    (0 : Vec n) ∈ subdifferential F x ↔ ∀ z, F x ≤ F z := by
  simp [mem_subdifferential, dot, sub_nonneg]

theorem subdifferential_eq_singleton_of_hasFDerivAt {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    subdifferential F x = {g} := by
  ext a
  constructor
  · intro ha
    exact supporting_vector_eq_gradient ha hg
  · rintro rfl
    exact convex_supporting_inequality hF hg

end ConvexSubdifferential
end BfgsVerification
