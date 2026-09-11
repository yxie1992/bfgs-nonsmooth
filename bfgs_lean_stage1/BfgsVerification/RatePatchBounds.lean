import BfgsVerification.FiniteRatePatch
import BfgsVerification.PlanarBranchGeometry

noncomputable section
open scoped BigOperators Topology ContDiff NNReal Manifold
open Matrix Filter Set Metric
namespace BfgsVerification.ConstantRankFields
open AffineCriticalObjective ConvexSubdifferential CenteredSmoothSublinear

/-- One positive radius ensures that every chart contributing at the later
endpoint contains both endpoints in its half-radius compact ball. -/
theorem FiniteRatePatch.buffer_radius {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q) :
    ∃δ : ℝ,0<δ ∧ ∀i : Fin P.size,∀x z : Vec n,
      P.cutoff i z≠0 → ‖z-x‖<δ →
        x∈closedBall (P.center i) ((P.chart i).radius/2) ∧
        z∈closedBall (P.center i) ((P.chart i).radius/2) := by
  obtain ⟨δ,hδ,hδi⟩ := finite_positive_lower_bound Finset.univ
    (fun i : Fin P.size => (P.chart i).radius/4)
    (fun i _ => by linarith [(P.chart i).radius_pos])
  refine ⟨δ,hδ,?_⟩
  intro i x z hi hstep
  have hz := P.small_of_cutoff_ne_zero hi
  have he := hδi i (Finset.mem_univ i)
  have hxz : dist x z<δ := by simpa only [dist_eq_norm,norm_sub_rev] using hstep
  constructor
  · have ht := dist_triangle x z (P.center i)
    change dist z (P.center i)<(P.chart i).radius/4 at hz
    change dist x (P.center i)≤(P.chart i).radius/2
    linarith
  · exact (show dist z (P.center i)<(P.chart i).radius/4 from hz).le.trans
      (by linarith [(P.chart i).radius_pos])

theorem FiniteRatePatch.uniform_one_sided {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q) :
    ∃L : ℝ,0<L ∧ ∀i : Fin P.size,∀j : Fin m,
      ∀x∈closedBall (P.center i) ((P.chart i).radius/2),
      ∀z∈closedBall (P.center i) ((P.chart i).radius/2),
        sqNorm (coordinateGradient (f j) z-coordinateGradient (f j) x) ≤
          2*L*(f j z-f j x-dot (coordinateGradient (f j) x) (z-x)) := by
  classical
  choose L hL hbound using (fun i : Fin P.size => fun j : Fin m => (P.chart i).one_sided_bounds j)
  let M : ℝ := 1+∑i,∑j,L i j
  have hM : 0<M := by
    dsimp [M]
    have hs : 0≤∑i,∑j,L i j := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hL i j).le))
    linarith
  refine ⟨M,hM,?_⟩
  intro i j x hx z hz
  have hLij : L i j≤M := by
    have h1 : L i j≤∑j,L i j := Finset.single_le_sum (fun j _ => (hL i j).le) (Finset.mem_univ j)
    have h2 : (∑j,L i j)≤∑i,∑j,L i j := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => (hL i j).le)) (Finset.mem_univ i)
    exact (h1.trans h2).trans (by dsimp [M]; linarith)
  have hb := hbound i j x hx z hz
  have hnonneg : 0≤f j z-f j x-dot (coordinateGradient (f j) x) (z-x) := by
    have h0 := sqNorm_nonneg (coordinateGradient (f j) z-coordinateGradient (f j) x)
    nlinarith [hL i j]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hnonneg)

theorem FiniteRatePatch.field_bound {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q)
    (hQ : IsCompact Q) : ∃G : ℝ,0<G ∧ ∀x∈Q,sqNorm (P.field x)≤G^2 := by
  obtain ⟨B,hB⟩ := hQ.bddAbove_image
    ((continuous_sqNorm.comp P.fieldC1.continuous).continuousOn)
  refine ⟨Real.sqrt (|B|+1),Real.sqrt_pos.mpr (by positivity),?_⟩
  intro x hx
  rw [Real.sq_sqrt (by positivity : 0≤|B|+1)]
  exact (hB ⟨x,hx,rfl⟩).trans (by linarith [le_abs_self B])

/-- The later field pairs to one with every branch active at the earlier
endpoint. The buffer applies to each nonzero cutoff, not only one chart. -/
theorem FiniteRatePatch.cross_pairing {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q)
    {x z : Vec n} (hz : z∈Q)
    (hbuffer : ∀i : Fin P.size,P.cutoff i z≠0 →
      x∈closedBall (P.center i) ((P.chart i).radius/2) ∧
      z∈closedBall (P.center i) ((P.chart i).radius/2))
    {j : Fin m} (hj : j∈activeIndices F f x) :
    dot (coordinateGradient (f j) z) (P.field z)=1 := by
  apply P.pairing_of_local hz
  intro i hi
  obtain ⟨hx,hz⟩ := hbuffer i hi
  have hx' : x∈ball (P.center i) (P.chart i).radius :=
    (show dist x (P.center i)≤(P.chart i).radius/2 from hx).trans_lt
      (by linarith [(P.chart i).radius_pos])
  have hz' : z∈ball (P.center i) (P.chart i).radius :=
    (show dist z (P.center i)≤(P.chart i).radius/2 from hz).trans_lt
      (by linarith [(P.chart i).radius_pos])
  exact (P.chart i).originalPairing z hz' j ((P.chart i).activeSubset x hx' hj)

end BfgsVerification.ConstantRankFields
