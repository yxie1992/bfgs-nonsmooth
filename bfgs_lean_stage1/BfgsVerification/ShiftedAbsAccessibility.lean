import BfgsVerification.ScalarCounterexamples
import BfgsVerification.AccessibleCurvatureBridge

/-! An actual-objective distinction between accessible jumps and all active
gradient differences in source G.4. The Wolfe constant is 1/4, different from
the 1/2 constant in the source's shifted-absolute-value nonnecessity example. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.ShiftedAbsAccessibility
open ScalarCounterexamples OneDimensional TransportedCertificate

theorem actual_scalar_derivative {x g : Vec 1}
    (hg : HasFDerivAt shiftedObjective (gradientFunctional g) x) :
    HasDerivAt shiftedAbs (g 0) (x 0) := by
  have hemb : HasDerivAt embed (embed 1) (x 0) := embed.hasFDerivAt.hasDerivAt
  have h := hg.comp_hasDerivAt_of_eq (x 0) hemb (embed_eval x).symm
  simpa [shiftedObjective, gradientFunctional_apply, dot] using h

theorem shiftedAbs_not_differentiable_zero : ¬ DifferentiableAt ℝ shiftedAbs 0 := by
  intro h
  have hq : DifferentiableAt ℝ (fun t : ℝ => (t+2)^2/2) 0 := by fun_prop
  have hsub := h.sub hq
  have he : (fun t : ℝ => shiftedAbs t-(t+2)^2/2) = abs := by
    funext t
    simp only [shiftedAbs, add_sub_cancel_left]
  rw [he] at hsub
  exact not_differentiableAt_abs_zero hsub

theorem actual_endpoint_ne_zero {x g : Vec 1}
    (hg : HasFDerivAt shiftedObjective (gradientFunctional g) x) : x 0 ≠ 0 := by
  intro hx
  have hd := (actual_scalar_derivative hg).differentiableAt
  rw [hx] at hd
  exact shiftedAbs_not_differentiable_zero hd

theorem actual_gradient_pos {x g : Vec 1}
    (hg : HasFDerivAt shiftedObjective (gradientFunctional g) x) (hx : 0 < x 0) :
    g 0 = x 0+3 := (actual_scalar_derivative hg).unique (shiftedAbs_hasDerivAt_pos hx)

theorem actual_gradient_neg {x g : Vec 1}
    (hg : HasFDerivAt shiftedObjective (gradientFunctional g) x) (hx : x 0 < 0) :
    g 0 = x 0+1 := (actual_scalar_derivative hg).unique (shiftedAbs_hasDerivAt_neg hx)

theorem no_small_right_left_crossing {c₁ : ℝ} {x z g h : Vec 1}
    (e : EligiblePair shiftedObjective c₁ (1/4) x z g h)
    (hd : pairDecrease x z g ≤ 1/4) (hx : 0 < x 0) (hz : z 0 < 0) : False := by
  have hg := actual_gradient_pos e.gradient_x hx
  have hh := actual_gradient_neg e.gradient_z hz
  have hd' : (x 0+3)*(x 0-z 0) ≤ 1/4 := by
    simpa [pairDecrease, pairStep, dot, hg, neg_mul, mul_sub] using hd
  have ht := e.curvature
  simp only [pairDecrease, pairCurvature, pairStep, dot, Fin.sum_univ_one, Pi.sub_apply, hg, hh] at ht
  have hw : 0 < x 0-z 0 := by linarith
  have hwidth : x 0-z 0 ≤ 1/12 := by
    nlinarith [mul_nonneg hx.le hw.le]
  have hgap : 0 < (z 0+1)-(1/4)*(x 0+3) := by linarith
  nlinarith [mul_pos hgap hw]

theorem no_small_left_right_crossing {c₁ : ℝ} (hc₁ : 0 < c₁) {x z g h : Vec 1}
    (e : EligiblePair shiftedObjective c₁ (1/4) x z g h)
    (hd : pairDecrease x z g ≤ 1/4) (hx : x 0 < 0) (hz : 0 < z 0) : False := by
  have hg := actual_gradient_neg e.gradient_x hx
  have hw : 0 < z 0-x 0 := by linarith
  have hdpos : 0 < -(x 0+1)*(z 0-x 0) := by
    have hp := e.decrease_pos
    simp only [pairDecrease, pairStep, dot, Fin.sum_univ_one, Pi.sub_apply, hg] at hp
    nlinarith
  have hgneg : x 0+1 < 0 := by
    exact neg_pos.mp ((mul_pos_iff_of_pos_right hw).mp hdpos)
  have hdec : shiftedAbs (z 0) < shiftedAbs (x 0) := by
    have ha := e.armijo
    have hp := mul_pos hc₁ e.decrease_pos
    change c₁*pairDecrease x z g ≤ shiftedAbs (x 0)-shiftedAbs (z 0) at ha
    linarith
  simp only [shiftedAbs, abs_of_neg hx, abs_of_pos hz] at hdec
  have hx2 : x 0 < -2 := by
    apply lt_of_not_ge
    intro hn
    have hn' : 0 ≤ x 0+2 := by linarith
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hx.le hn', sq_nonneg (z 0)]
  have hd' : -(x 0+1)*(z 0-x 0) ≤ 1/4 := by
    simp only [pairDecrease, pairStep, dot, Fin.sum_univ_one, Pi.sub_apply, hg] at hd
    nlinarith
  have hprod := mul_pos (show 0 < -(x 0+1)-1 by linarith) (show 0 < z 0-x 0-2 by linarith)
  nlinarith

/-- Every sufficiently small eligible pair remains on one smooth side of the
kink, with all actual endpoint gradients quantified. -/
theorem small_eligible_same_side {c₁ : ℝ} (hc₁ : 0 < c₁) {x z g h : Vec 1}
    (e : EligiblePair shiftedObjective c₁ (1/4) x z g h)
    (hd : pairDecrease x z g ≤ 1/4) :
    (0 < x 0 ∧ 0 < z 0) ∨ (x 0 < 0 ∧ z 0 < 0) := by
  rcases lt_or_gt_of_ne (actual_endpoint_ne_zero e.gradient_x) with hx|hx
  · rcases lt_or_gt_of_ne (actual_endpoint_ne_zero e.gradient_z) with hz|hz
    · exact Or.inr ⟨hx,hz⟩
    · exact (no_small_left_right_crossing hc₁ e hd hx hz).elim
  · rcases lt_or_gt_of_ne (actual_endpoint_ne_zero e.gradient_z) with hz|hz
    · exact (no_small_right_left_crossing e hd hx hz).elim
    · exact Or.inl ⟨hx,hz⟩

theorem small_eligible_gradient_change {c₁ : ℝ} (hc₁ : 0 < c₁) {x z g h : Vec 1}
    (e : EligiblePair shiftedObjective c₁ (1/4) x z g h)
    (hd : pairDecrease x z g ≤ 1/4) : h-g = z-x := by
  have he : h 0-g 0 = z 0-x 0 := by
    rcases small_eligible_same_side hc₁ e hd with hp|hn
    · rw [actual_gradient_pos e.gradient_x hp.1,actual_gradient_pos e.gradient_z hp.2]
      ring
    · rw [actual_gradient_neg e.gradient_x hn.1,actual_gradient_neg e.gradient_z hn.2]
      ring
  ext i
  fin_cases i
  exact he

def identityCertificate {K : Set (Vec 1)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    {c₁ : ℝ} (hc₁ : 0 < c₁) :
    BandCertificate shiftedObjective K (shiftedObjective (embed (-1))) c₁ (1/4) η := by
  have hex := scalar_gradient_band_bounds shiftedObjective_convex (embed (-1)) hK hη
  let m := hex.choose
  have hm : 0 < m := hex.choose_spec.choose_spec.1
  have hbound := hex.choose_spec.choose_spec.2.2
  refine { W := fun _ => 1
           m := m^2
           C := 1
           L := 0
           δ := 1/4
           m_pos := sq_pos_of_pos hm
           L_nonneg := le_rfl
           delta_pos := by norm_num
           positive_semidefinite := fun _ _ _ => Matrix.PosSemidef.one
           visibility := ?_
           secant := ?_
           transport := ?_ }
  · intro x hx g hg
    have hb := (hbound x hx g hg).1
    rw [scalar_energy]
    simp only [Matrix.one_apply_eq, one_mul]
    nlinarith [sq_abs (g 0), abs_nonneg (g 0)]
  · intro x z g h _ _ e hd
    have he := small_eligible_gradient_change hc₁ e hd
    simp only [he, pairCurvature, pairStep, metricEnergy, Matrix.one_mulVec, one_mul, dot, sqNorm]
    exact le_rfl
  · intro x z g h _ _ e hd
    simp only [zero_mul, add_zero, one_smul, sub_self]
    exact Matrix.PosSemidef.zero

theorem identityCertificate_field {K : Set (Vec 1)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    {c₁ : ℝ} (hc₁ : 0 < c₁) : (identityCertificate hK hη hc₁).W = fun _ => 1 := rfl

theorem shifted_all_compact_band_certificates {K : Set (Vec 1)} (hK : IsCompact K)
    {c₁ : ℝ} (hc₁ : 0 < c₁) :
    HasBandCertificates shiftedObjective K (shiftedObjective (embed (-1))) c₁ (1/4) :=
  fun _η hη _ => ⟨identityCertificate hK hη hc₁⟩

def activeGradients : Fin 2 → Vec 1 := ![embed 1,embed 3]
def activeApproach (i : Fin 2) (k : ℕ) : Vec 1 :=
  ![crossingZ (crossingScale k),crossingX (crossingScale k)] i
def activeGradientApproach (i : Fin 2) (k : ℕ) : Vec 1 :=
  ![crossingH (crossingScale k),crossingG (crossingScale k)] i

theorem active_approach_actual_gradient (i : Fin 2) (k : ℕ) :
    HasFDerivAt shiftedObjective (gradientFunctional (activeGradientApproach i k))
      (activeApproach i k) := by
  fin_cases i
  · exact (crossing_gradients (crossingScale_pos k)).2
  · exact (crossing_gradients (crossingScale_pos k)).1

theorem active_approach_tendsto (i : Fin 2) : Tendsto (activeApproach i) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i
  · simpa only [activeApproach, Fin.isValue, Matrix.cons_val_zero, crossingZ, embed_apply,
      Pi.zero_apply, neg_zero, zero_div] using crossingScale_tendsto.neg.div_const 2
  · simpa only [activeApproach, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, crossingX,
      embed_apply, Pi.zero_apply] using crossingScale_tendsto

theorem active_gradient_approach_tendsto (i : Fin 2) :
    Tendsto (activeGradientApproach i) atTop (𝓝 (activeGradients i)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i
  · simpa only [activeGradientApproach, activeGradients, Fin.isValue, Matrix.cons_val_zero,
      crossingH, embed_apply, zero_div, sub_zero] using (crossingScale_tendsto.div_const 2).const_sub 1
  · simpa only [activeGradientApproach, activeGradients, Fin.isValue, Matrix.cons_val_one,
      Matrix.head_cons, crossingG, embed_apply, add_zero] using crossingScale_tendsto.const_add 3

theorem active_approach_in_band (i : Fin 2) (k : ℕ) :
    activeApproach i k ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1/4) := by
  fin_cases i
  · exact (crossing_band (crossingScale_pos k) (crossingScale_le k)).2
  · exact (crossing_band (crossingScale_pos k) (crossingScale_le k)).1

theorem active_gradient_identity_visibility (i : Fin 2) :
    0 < metricEnergy (1 : Mat 1) (activeGradients i) := by
  fin_cases i <;> norm_num [activeGradients, metricEnergy, dot, Fin.sum_univ_one, embed_apply]

theorem active_common_tangent_zero (i : Fin 2) :
    (AccessibleJumpGeometry.tangentSpace (fun j => euclideanVector (activeGradients j))).orthogonalProjection
      (euclideanVector (activeGradients i)) = 0 := by
  rw [AccessibleJumpGeometry.common_tangential_projection _ i 0]
  rw [Submodule.orthogonalProjection_eq_zero_iff]
  change euclideanVector (activeGradients 0) ∈
    (AccessibleJumpGeometry.jumpSpace (fun j => euclideanVector (activeGradients j)))ᗮᗮ
  rw [Submodule.orthogonal_orthogonal]
  have hd := vsub_mem_vectorSpan ℝ
    (Set.mem_range_self (f := fun j => euclideanVector (activeGradients j)) (1 : Fin 2))
    (Set.mem_range_self (f := fun j => euclideanVector (activeGradients j)) (0 : Fin 2))
  have hm := (AccessibleJumpGeometry.jumpSpace (fun j => euclideanVector (activeGradients j))).smul_mem
    (1/2 : ℝ) hd
  have he : (1/2 : ℝ) • (euclideanVector (activeGradients 1)-euclideanVector (activeGradients 0)) =
      euclideanVector (activeGradients 0) := by
    ext j
    norm_num [activeGradients, euclideanVector, embed_apply]
  simpa only [vsub_eq_sub,he] using hm

theorem full_active_tangent_space_eq_bot :
    AccessibleJumpGeometry.tangentSpace (fun j => euclideanVector (activeGradients j)) = ⊥ := by
  have hp := active_common_tangent_zero 0
  rw [Submodule.orthogonalProjection_eq_zero_iff] at hp
  change euclideanVector (activeGradients 0) ∈
    (AccessibleJumpGeometry.jumpSpace (fun j => euclideanVector (activeGradients j)))ᗮᗮ at hp
  rw [Submodule.orthogonal_orthogonal] at hp
  have htop : AccessibleJumpGeometry.jumpSpace (fun j => euclideanVector (activeGradients j)) = ⊤ := by
    apply top_unique
    intro v _
    have hm := (AccessibleJumpGeometry.jumpSpace (fun j => euclideanVector (activeGradients j))).smul_mem
      (v 0) hp
    have he : v 0 • euclideanVector (activeGradients 0) = v := by
      ext j
      fin_cases j
      simp [activeGradients,euclideanVector,embed_apply]
    rwa [he] at hm
  simp only [AccessibleJumpGeometry.tangentSpace,htop,Submodule.top_orthogonal_eq_bot]

theorem kink_nondifferentiable : ¬ DifferentiableAt ℝ shiftedObjective (0 : Vec 1) := by
  intro hd
  have hn := actual_endpoint_ne_zero (hasFDerivAt_coordinateGradient hd)
  exact hn rfl

theorem kink_positive_band :
    (0 : Vec 1) ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1/4) := by
  norm_num [positiveBand,shiftedObjective,shiftedAbs,embed_apply]

theorem kink_nonoptimal : shiftedObjective (embed (-1)) < shiftedObjective (0 : Vec 1) := by
  norm_num [shiftedObjective,shiftedAbs,embed_apply]

/-- There is no nonzero limiting jump along actual eligible pairs converging
to the kink with vanishing curvature. The small-decrease condition is derived
from weak Wolfe, not imposed as a separate accessibility premise. -/
theorem accessible_jump_zero {ι : Type*} {l : Filter ι} [NeBot l]
    {c₁ : ℝ} (hc₁ : 0 < c₁) (x z g h : ι → Vec 1) (p jump : Vec 1)
    (he : ∀ᶠ a in l, EligiblePair shiftedObjective c₁ (1/4) (x a) (z a) (g a) (h a))
    (hx : Tendsto x l (𝓝 p)) (hz : Tendsto z l (𝓝 p))
    (ht : Tendsto (fun a => pairCurvature (x a) (z a) (g a) (h a)) l (𝓝 0))
    (hy : Tendsto (fun a => h a-g a) l (𝓝 jump)) : jump = 0 := by
  have hd := AccessibleJumpGeometry.eligible_decrease_tendsto_zero_of_curvature
    (by norm_num : (1/4 : ℝ) < 1) x z g h he ht
  have heq : (fun a => h a-g a) =ᶠ[l] (fun a => z a-x a) := by
    filter_upwards [he,hd.eventually_le_const (by norm_num : (0 : ℝ) < 1/4)] with a ha hsmall
    exact small_eligible_gradient_change hc₁ ha hsmall
  have hzlim : Tendsto (fun a => z a-x a) l (𝓝 0) := by simpa only [sub_self] using hz.sub hx
  exact tendsto_nhds_unique hy (hzlim.congr' heq.symm)

/-- Actual finite convex objective, genuine limiting gradients in a fixed
compact positive band, and a continuous constant-I transported certificate.
Its full active-difference tangent projection is zero despite strict visibility.
This refutes only the unqualified all-active tangent necessity. -/
theorem objective_level_accessibility_counterexample :
    ∃ B : BandCertificate shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1/8) (1/4) (1/4),
      B.W = (fun _ => 1) ∧ Continuous B.W ∧
      (∀ i k, HasFDerivAt shiftedObjective (gradientFunctional (activeGradientApproach i k))
        (activeApproach i k)) ∧
      (∀ i, Tendsto (activeApproach i) atTop (𝓝 0) ∧
        Tendsto (activeGradientApproach i) atTop (𝓝 (activeGradients i))) ∧
      (∀ i k, activeApproach i k ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1/4)) ∧
      (∀ i, 0 < metricEnergy (B.W 0) (activeGradients i)) ∧
      (∀ i, (AccessibleJumpGeometry.tangentSpace (fun j => euclideanVector (activeGradients j))).orthogonalProjection
        (euclideanVector (activeGradients i)) = 0) := by
  let B := identityCertificate (shiftedObjective_sublevel_compact 3)
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) < 1/8)
  refine ⟨B,rfl,continuous_const,active_approach_actual_gradient,
    fun i => ⟨active_approach_tendsto i,active_gradient_approach_tendsto i⟩,
    active_approach_in_band,active_gradient_identity_visibility,active_common_tangent_zero⟩

end BfgsVerification.ShiftedAbsAccessibility
