import BfgsVerification.PlanarTransportAlgebra
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv

/-! One-sided comparison for C's logarithmic transport. This works through
arbitrarily many switching points: no partition or almost-everywhere
fundamental theorem is assumed. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification
namespace PlanarScalarTransport

/-- A convex-decrease derivative budget controls every continuous observable
whose right derivative is dominated by the absolute objective right derivative.
The actual convex objective supplies the lower derivative bound separately. -/
theorem right_derivative_transport_budget {φ h φ' h' : ℝ → ℝ} {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hφ : ContinuousOn φ (Icc 0 1)) (hh : ContinuousOn h (Icc 0 1))
    (hφ' : ∀ t ∈ Ico 0 1, HasDerivWithinAt φ (φ' t) (Ici t) t)
    (hh' : ∀ t ∈ Ico 0 1, HasDerivWithinAt h (h' t) (Ici t) t)
    (hlower : ∀ t ∈ Ico 0 1, -d ≤ φ' t)
    (hbound : ∀ t ∈ Ico 0 1, |h' t| ≤ C*|φ' t|)
    (hdescent : φ 1 ≤ φ 0) : |h 1-h 0| ≤ 2*C*d := by
  let B : ℝ → ℝ := fun t => C*(φ t-φ 0+2*d*t)
  have hB : ContinuousOn B (Icc 0 1) := by
    dsimp [B]
    fun_prop
  have hB' : ∀ t ∈ Ico 0 1,
      HasDerivWithinAt B (C*(φ' t+2*d)) (Ici t) t := by
    intro t ht
    dsimp [B]
    convert (((hφ' t ht).sub_const (φ 0)).add
      ((hasDerivWithinAt_id t (Ici t)).const_mul (2*d))).const_mul C using 1 <;> ring
  have hobs : ContinuousOn (fun t => h t-h 0) (Icc 0 1) := hh.sub continuousOn_const
  have hobs' : ∀ t ∈ Ico 0 1,
      HasDerivWithinAt (fun t => h t-h 0) (h' t) (Ici t) t :=
    fun t ht => (hh' t ht).sub_const _
  have hb : ∀ t ∈ Ico 0 1, ‖h' t‖ ≤ C*(φ' t+2*d) := by
    intro t ht
    rw [Real.norm_eq_abs]
    apply (hbound t ht).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact abs_le.mpr ⟨by linarith [hlower t ht], by linarith [hlower t ht]⟩
  have hx := image_norm_le_of_norm_deriv_right_le_deriv_boundary' hobs hobs'
    (show ‖h 0-h 0‖ ≤ B 0 by simp [B]) hB hB' hb
    (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  rw [Real.norm_eq_abs] at hx
  apply hx.trans
  dsimp [B]
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hdescent)]

/-- The initial accepted derivative is a lower bound for every subsequent
actual convex right derivative, including the initial point. -/
theorem convex_right_derivative_lower {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    {d : ℝ} (h0 : HasDerivAt φ (-d) 0) {t : ℝ} (ht : 0 ≤ t) :
    -d ≤ derivWithin φ (Ioi t) t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [h0.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)]
  · exact (hφ.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) ht h0).trans
      ((hφ.slope_le_leftDeriv_of_mem_interior (mem_univ _) (by simp) ht).trans
        (hφ.leftDeriv_le_rightDeriv_of_mem_interior (by simp)))

/-- All scalar derivative-budget premises are discharged from convexity and
the actual initial derivative. The remaining observable derivative estimate
is the local geometric input to C's transport argument. -/
theorem convex_transport_budget {φ h h' : ℝ → ℝ} {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hφ : ConvexOn ℝ univ φ)
    (h0 : HasDerivAt φ (-d) 0) (hh : ContinuousOn h (Icc 0 1))
    (hh' : ∀ t ∈ Ico 0 1, HasDerivWithinAt h (h' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 1, |h' t| ≤ C*|derivWithin φ (Ioi t) t|)
    (hdescent : φ 1 ≤ φ 0) : |h 1-h 0| ≤ 2*C*d := by
  have hc : Continuous φ := continuous_iff_continuousOn_univ.mpr (hφ.continuousOn isOpen_univ)
  exact right_derivative_transport_budget hC hd hc.continuousOn hh
    (fun t _ => (hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)).Ici_of_Ioi)
    hh' (fun t ht => convex_right_derivative_lower hφ h0 ht.1) hbound hdescent

/-- Nonvanishing throughout the whole segment forces the determinant ratio
to be positive; the endpoint signs are not assumed. -/
theorem positive_endpoint_ratio {D : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 1))
    (hne : ∀ t ∈ Icc 0 1, D t ≠ 0) : 0 < D 1/D 0 := by
  have h0 := hne 0 (by norm_num)
  have h1 := hne 1 (by norm_num)
  apply div_pos_iff.mpr
  rcases lt_or_gt_of_ne h0 with h0 | h0
  · right
    refine ⟨?_,h0⟩
    by_contra hn
    have h1pos : 0 ≤ D 1 := le_of_not_gt hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hD
      (show (0:ℝ)∈Icc (D 0) (D 1) from ⟨h0.le,h1pos⟩)
    exact hne t ht he
  · left
    refine ⟨?_,h0⟩
    by_contra hn
    have h1neg : D 1 ≤ 0 := le_of_not_gt hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ)≤1) hD
      (show (0:ℝ)∈Icc (D 1) (D 0) from ⟨h1neg,h0.le⟩)
    exact hne t ht he

/-- The logarithmic transport budget follows from actual right derivatives
of the determinant and convex objective, even at switching points. -/
theorem convex_log_determinant_budget {φ D D' : ℝ → ℝ} {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hφ : ConvexOn ℝ univ φ)
    (h0 : HasDerivAt φ (-d) 0) (hD : ContinuousOn D (Icc 0 1))
    (hne : ∀ t ∈ Icc 0 1, D t ≠ 0)
    (hD' : ∀ t ∈ Ico 0 1, HasDerivWithinAt D (D' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 1, |D' t/D t| ≤ C*|derivWithin φ (Ioi t) t|)
    (hdescent : φ 1 ≤ φ 0) :
    0 < D 1/D 0 ∧ |Real.log (D 1/D 0)| ≤ 2*C*d := by
  refine ⟨positive_endpoint_ratio hD hne, ?_⟩
  have h := convex_transport_budget hC hd hφ h0 (hD.log hne)
    (fun t ht => (hD' t ht).log (hne t (Ico_subset_Icc_self ht))) hbound hdescent
  rwa [← Real.log_div (hne 1 (by norm_num)) (hne 0 (by norm_num))] at h

/-- For an actual planar field the determinant budget yields the literal
transport identity and a positive scalar, by solving in the actual step/frame
basis. No transport coefficients are assumed. -/
theorem planar_transport_from_right_derivative_budget
    {φ : ℝ → ℝ} {W : Vec 2 → Vec 2} {x s : Vec 2} {D' : ℝ → ℝ} {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hφ : ConvexOn ℝ univ φ)
    (h0 : HasDerivAt φ (-d) 0)
    (hD : ContinuousOn (fun t : ℝ => HomogeneousPlanar.pairDet s (W (x+t • s))) (Icc 0 1))
    (hne : ∀ t : ℝ, t ∈ Icc 0 1 → HomogeneousPlanar.pairDet s (W (x+t • s)) ≠ 0)
    (hD' : ∀ t ∈ Ico 0 1,
      HasDerivWithinAt (fun t : ℝ => HomogeneousPlanar.pairDet s (W (x+t • s))) (D' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 1,
      |D' t/HomogeneousPlanar.pairDet s (W (x+t • s))| ≤ C*|derivWithin φ (Ioi t) t|)
    (hdescent : φ 1 ≤ φ 0) :
    ∃ lam β : ℝ, 0 < lam ∧ W (x+s)=lam • W x+β • s ∧ |Real.log lam| ≤ 2*C*d := by
  have h := convex_log_determinant_budget hC hd hφ h0 hD hne hD' hbound hdescent
  simp only [one_smul,zero_smul,add_zero] at h
  refine ⟨_,_,h.1,PlanarTransport.determinant_transport s (W x) (W (x+s)) ?_,h.2⟩
  simpa using hne 0 (by norm_num)

end PlanarScalarTransport
end BfgsVerification
