import BfgsVerification.PlanarMaxRegular

/-! C's nondegenerate finite smooth-max corollary, with actual active
restriction and geometric hypotheses derived before the BFGS run is chosen. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Metric
namespace BfgsVerification
namespace PlanarMaxRegular
open ConvexSubdifferential PlanarCornerCharts AffineCriticalObjective AffineBarycentric

theorem finite_max_local_basin {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec 2) (hmin : ∀ x, F star≤F x) (hunique : ∀ x, F x=F star → x=star)
    {m : ℕ} {f : Fin m → Vec 2 → ℝ} {U : Set (Vec 2)}
    (hU : IsOpen U) (hstar : star∈U) (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hrep : LocalFiniteMax F f star)
    (hind : AffineIndependent ℝ (fun i => coordinateGradient (f (activeIndexMap F f star i)) star))
    (w : Vec (activeIndices F f star).card) (hw : ∀ i, 0<w i)
    (hsum : ∑ i, w i=1)
    (hzero : ∑ i, w i • coordinateGradient (f (activeIndexMap F f star i)) star=0)
    {b : ℝ} (hb : F star<b)
    (hstrict : ∀ ℓ : ℝ, F star<ℓ → ℓ≤b →
      ∀ x y : Vec 2, segment ℝ x y⊆frontier {z | F z≤ℓ} → x=y) :
    ∃ ε : ℝ, 0<ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0)<F star+ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  let a := activeIndexMap F f star
  let g : Vec 2 → Fin (activeIndices F f star).card → Vec 2 :=
    fun p i => coordinateGradient (f (a i)) p
  have hd (p : Vec 2) (hp : p∈U) (i : Fin m) :
      HasFDerivAt (f i) (gradientFunctional (coordinateGradient (f i) p)) p :=
    hasFDerivAt_coordinateGradient (((hf i).2.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num))
  have hr := localFiniteMax_restrict_active (convex_continuous hF).continuousAt
    (fun i => (hd star hstar i).continuousAt) hrep
  have hg : ∀ᶠ p in 𝓝 star, ∀ i, HasFDerivAt (f (a i)) (gradientFunctional (g p i)) p := by
    filter_upwards [hU.mem_nhds hstar] with p hp i
    exact hd p hp (a i)
  have hc (i) : ContinuousAt (fun p => g p i) star :=
    (PlanarCrossing.contDiffAt_coordinateGradient ((hf (a i)).2.contDiffAt (hU.mem_nhds hstar))).continuousAt
  have hbary := local_affine_critical_correctness hF g star hr hg hc hind w hw hsum hzero
  have he : ∀ᶠ p in 𝓝 star,
      (¬IsAffineCritical F p → ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) ∧ AffineCorrectAt F p := by
    filter_upwards [hU.mem_nhds hstar,hr.eventually,hbary] with p hp hrp hbp
    constructor
    · intro hn
      exact regular_of_finite_max_independent hF hU hp (fun i => hf (a i)) hrp hbp.1 hn
    · intro hcrit
      apply zero_mem_iff_global_minimum.mpr
      exact hbp.2.1.mp ((isAffineCritical_iff_coordinate_affineSpan F p).mp hcrit)
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp he
  exact PlanarConvergence.local_convergence_basin hF star hmin hunique isOpen_ball
    (mem_ball_self hrpos) (fun p hp => (hball hp).1) (fun p hp => (hball hp).2) hb hstrict

end PlanarMaxRegular
end BfgsVerification
