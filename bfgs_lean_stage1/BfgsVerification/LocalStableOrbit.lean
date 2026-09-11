import BfgsVerification.StableSequence
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear

noncomputable section
open scoped Topology ZeroAtInfty NNReal
open Set Filter
namespace BfgsVerification.LocalStableOrbit

variable {S U : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

theorem small_lipschitz_ball {N : S×U → S×U} (hN : HasStrictFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0)
    {δ r : ℝ} (hδ : 0<δ) (hr : 0<r) :
    ∃ R : ℝ, 0<R ∧ R≤r ∧ ∀ x y, ‖x‖≤R → ‖y‖≤R → ‖N x-N y‖≤δ*‖x-y‖ := by
  obtain ⟨V,hV,hLip⟩ := hN.exists_lipschitzOnWith_of_nnnorm_lt ⟨δ,hδ.le⟩ (by simpa using hδ)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hV
  let R := min r (eps/2)
  have hR : 0<R := lt_min hr (half_pos heps)
  have hmem {x : S×U} (hx : ‖x‖≤R) : x∈V := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact (hx.trans (min_le_right _ _)).trans_lt (half_lt_self heps)
  exact ⟨R,hR,min_le_left _ _,fun x y hx hy =>
    (lipschitzOnWith_iff_norm_sub_le.mp hLip) (hmem hx) (hmem hy)⟩

theorem contraction_parameters (A : S →L[ℝ] S) (B : U →L[ℝ] U)
    (hA : ‖A‖<1) (hB : ‖B‖<1) :
    ∃ δ : ℝ, 0<δ ∧ ∃ K : ℝ≥0, K<1 ∧ ‖A‖+δ≤K ∧ ‖B‖*(1+δ)≤K := by
  let δ := min ((1-‖A‖)/2) ((1-‖B‖)/2)
  have hδ : 0<δ := lt_min (by linarith) (by linarith)
  have ha : ‖A‖+δ<1 := by have hh := min_le_left ((1-‖A‖)/2) ((1-‖B‖)/2); dsimp [δ]; linarith
  have hb : ‖B‖*(1+δ)<1 := by
    have hh := min_le_right ((1-‖A‖)/2) ((1-‖B‖)/2)
    have hm := mul_le_mul_of_nonneg_right hB.le hδ.le
    dsimp [δ] at *
    nlinarith
  let K : ℝ≥0 := ⟨max (‖A‖+δ) (‖B‖*(1+δ)), (add_nonneg (norm_nonneg _) hδ.le).trans (le_max_left _ _)⟩
  exact ⟨δ,hδ,K,max_lt ha hb,le_max_left _ _,le_max_right _ _⟩

theorem local_stable_orbits_from_remainder (A : S →L[ℝ] S) (L : U ≃L[ℝ] U)
    (N : S×U → S×U) (hN : HasStrictFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0) (hN0 : N 0=0)
    (hA : ‖A‖<1) (hB : ‖L.symm.toContinuousLinearMap‖<1) {r : ℝ} (hr : 0<r) :
    ∃ R : ℝ, 0<R ∧ ∀ a : S, ‖a‖≤R →
      ∃ w : ℕ → S×U, (∀ n, ‖w n‖≤r) ∧ Tendsto w atTop (𝓝 0) ∧
        (w 0).1=a ∧ ∀ n, w (n+1)=(A (w n).1,L (w n).2)+N (w n) := by
  obtain ⟨δ,hδ,K,hK,hAK,hBK⟩ := contraction_parameters A L.symm.toContinuousLinearMap hA hB
  obtain ⟨R,hR,hRr,hLip⟩ := small_lipschitz_ball hN hδ hr
  refine ⟨R,hR,?_⟩
  intro a ha
  obtain ⟨w,hw,ht,ha',hrec⟩ := nonlinear_stable_orbit A L N a hN.continuousAt hN0
    hR.le hδ.le hK ha hAK hBK hLip
  exact ⟨w,fun n => (hw n).trans hRr,ht,ha',hrec⟩

/-- A strict derivative with a contractive stable block and inverse-contracting
unstable block gives actual forward orbits in every prescribed neighborhood.
The stable coordinate of the initial point is freely prescribed. -/
theorem local_stable_orbits (A : S →L[ℝ] S) (L : U ≃L[ℝ] U) (T : S×U → S×U)
    (hT0 : T 0=0) (hT : HasStrictFDerivAt T (A.prodMap L.toContinuousLinearMap) 0)
    (hA : ‖A‖<1) (hB : ‖L.symm.toContinuousLinearMap‖<1) {r : ℝ} (hr : 0<r) :
    ∃ R : ℝ, 0<R ∧ ∀ a : S, ‖a‖≤R →
      ∃ w : ℕ → S×U, (∀ n, ‖w n‖≤r) ∧ Tendsto w atTop (𝓝 0) ∧
        (w 0).1=a ∧ ∀ n, w (n+1)=T (w n) := by
  let D := A.prodMap L.toContinuousLinearMap
  let N : S×U → S×U := fun x => T x-D x
  have hN : HasStrictFDerivAt N (0 : (S×U) →L[ℝ] (S×U)) 0 := by
    simpa only [D, sub_self] using hT.sub D.hasStrictFDerivAt
  have hN0 : N 0=0 := by simp [N,hT0]
  obtain ⟨R,hR,hsol⟩ := local_stable_orbits_from_remainder A L N hN hN0 hA hB hr
  refine ⟨R,hR,?_⟩
  intro a ha
  obtain ⟨w,hw,ht,ha',hrec⟩ := hsol a ha
  refine ⟨w,hw,ht,ha',?_⟩
  intro n
  calc
    w (n+1)=(A (w n).1,L (w n).2)+N (w n) := hrec n
    _=T (w n) := by
      change D (w n)+(T (w n)-D (w n))=T (w n)
      abel

end BfgsVerification.LocalStableOrbit
