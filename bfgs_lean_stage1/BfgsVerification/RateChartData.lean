import BfgsVerification.OriginalActiveRateChart
import BfgsVerification.CompactOneSided

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Matrix Filter Set Metric
namespace BfgsVerification.ConstantRankFields
open AffineCriticalObjective ConvexSubdifferential CenteredSmoothSublinear

/-- Local constancy of the actual original-active gradient-difference rank.
The active family is nonempty for a represented finite maximum. -/
def LocallyConstantActiveRank {n m : ℕ} (F : Vec n → ℝ)
    (f : Fin m → Vec n → ℝ) (p : Vec n) : Prop :=
  ∃i : Fin (activeIndices F f p).card,∀ᶠx in 𝓝 p,
    (differenceMatrix (fun j => coordinateGradient (f (activeIndexMap F f p j)) x) i).rank=
      (differenceMatrix (fun j => coordinateGradient (f (activeIndexMap F f p j)) p) i).rank

theorem locallyConstantActiveRank_all_bases {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {p : Vec n} (h : LocallyConstantActiveRank F f p)
    (i : Fin (activeIndices F f p).card) : ∀ᶠx in 𝓝 p,
      (differenceMatrix (fun j => coordinateGradient (f (activeIndexMap F f p j)) x) i).rank=
        (differenceMatrix (fun j => coordinateGradient (f (activeIndexMap F f p j)) p) i).rank := by
  obtain ⟨j,hj⟩ := h
  simpa only [differenceMatrix_rank] using hj

/-- Local data are constructed below from actual constant-rank objective
hypotheses, then used to patch one finite comparison field. -/
structure RateChart {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ) (p : Vec n) where
  radius : ℝ
  radius_pos : 0 < radius
  field : Vec n → Vec n
  fieldC1 : ContDiffOn ℝ 1 field (ball p radius)
  originalPairing : ∀x∈ball p radius,∀j∈activeIndices F f p,
    dot (coordinateGradient (f j) x) (field x)=1
  supportsPairing : ∀x∈ball p radius,∀a∈subdifferential F x,dot a (field x)=1
  activeSubset : ∀x∈ball p radius,activeIndices F f x⊆activeIndices F f p
  representation : ∀x∈ball p radius,LocalFiniteMax F f x
  branchC2 : ∀x∈ball p radius,∀j,ContDiffAt ℝ 2 (f j) x
  branchConvex : ∀j,ConvexOn ℝ (ball p radius) (f j)

theorem nonempty_rateChart {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (f : Fin m → Vec n → ℝ) (p : Vec n)
    (hrep : LocalFiniteMax F f p) (hf : ∀j,ContDiffAt ℝ 2 (f j) p)
    (hnc : ¬IsAffineCritical F p) (hrank : LocallyConstantActiveRank F f p)
    (hconv : ∃V : Set (Vec n),IsOpen V ∧ p∈V ∧ ∀j,ConvexOn ℝ V (f j)) :
    Nonempty (RateChart F f p) := by
  obtain ⟨i,hr⟩ := hrank
  obtain ⟨U,v,hU,hp,hv,hpair,hsupport,hdata⟩ :=
    original_active_commonRate_chart hF f p hrep hf hnc i hr
  obtain ⟨V,hV,hpV,hconv⟩ := hconv
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hp) (hV.mem_nhds hpV))
  exact ⟨{
    radius := r
    radius_pos := hr
    field := v
    fieldC1 := hv.mono (fun x hx => (hball hx).1)
    originalPairing := fun x hx => hpair x (hball hx).1
    supportsPairing := fun x hx => hsupport x (hball hx).1
    activeSubset := fun x hx => (hdata x (hball hx).1).1
    representation := fun x hx => (hdata x (hball hx).1).2.1
    branchC2 := fun x hx => (hdata x (hball hx).1).2.2
    branchConvex := fun j => (hconv j).subset (fun x hx => (hball hx).2) (convex_ball p r)
  }⟩

theorem locallyC11_of_contDiffOn {n : ℕ} {f : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) : LocallyC11On U f := by
  refine ⟨hf.differentiableOn (by norm_num),?_⟩
  intro x hx
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (by norm_num)
  obtain ⟨L,V,hV,hLip⟩ := hd.exists_lipschitzOnWith
  exact ⟨L,V,mem_nhdsWithin_of_mem_nhds hV,hLip⟩

/-- Each actual chart has uniform one-sided branch constants on the half-radius
closed ball; the required descent-test displacement remains in the full ball. -/
theorem RateChart.one_sided_bounds {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {p : Vec n} (c : RateChart F f p) (i : Fin m) :
    ∃L : ℝ,0 < L ∧ ∀x∈closedBall p (c.radius/2),∀z∈closedBall p (c.radius/2),
      sqNorm (coordinateGradient (f i) z-coordinateGradient (f i) x) ≤
        2*L*(f i z-f i x-dot (coordinateGradient (f i) x) (z-x)) := by
  apply exists_one_sided_constant_on_compact isOpen_ball (c.branchConvex i)
    (locallyC11_of_contDiffOn isOpen_ball (fun x hx => (c.branchC2 x hx i).contDiffWithinAt))
    (isCompact_closedBall _ _)
  intro x hx
  exact (show dist x p≤c.radius/2 from hx).trans_lt (by linarith [c.radius_pos])

end BfgsVerification.ConstantRankFields
