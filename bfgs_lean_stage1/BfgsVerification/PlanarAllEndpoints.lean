import BfgsVerification.PlanarAllEndpointField
import BfgsVerification.PlanarAllPairSource

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Metric
namespace BfgsVerification.PlanarAllPairs
open PlanarCornerCharts PlanarObjectiveField ConvexSubdifferential AffineCriticalObjective
open TransportedCertificate HomogeneousPlanar

/-- All three literal Module C endpoint estimates hold for the same actual
comparison field, every sufficiently close eligible pair, and one common
buffered neighborhood of the compact regular level. -/
theorem source_all_endpoint_estimates {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀x∈K,F x=ℓ)
    (hstrict : ∀x y : Vec 2,segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x=y)
    (hregular : ∀x∈K,ContDiffAt ℝ 2 F x ∨ ConvexTwoBranchRegularAt F x)
    (hnoncritical : ∀x∈K,¬IsAffineCritical F x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) :
    ∃m : ℕ,∃χ : Fin m → Vec 2 → ℝ,∃v : Fin m → ℝ → Vec 2,
      (∀i,ContDiff ℝ ∞ (χ i)) ∧ ∃U Q : Set (Vec 2),
      IsOpen U ∧ K⊆U ∧ closure U⊆Q ∧ IsCompact Q ∧
      ∃η κ δ C C' C₀ : ℝ,0 < η ∧ 0 < κ ∧ 0 < δ ∧ 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ C₀ ∧
      (∀x∈Q,∃L : ℝ≥0,∃V∈𝓝 x,LipschitzOnWith L (field hF χ v) V) ∧
      (∀x∈Q,∀g∈subdifferential F x,η ≤ dot g (field hF χ v x)) ∧
      (∀x∈Q,∀g∈subdifferential F x,∀h∈subdifferential F x,
        dot g (field hF χ v x)=dot h (field hF χ v x)) ∧
      ∀x∈U,∀z∈U,∀g h,EligiblePair F c₁ c₂ x z g h → ‖euclideanVector (z-x)‖ < δ →
        (∀θ∈Icc (0 : ℝ) 1,x+θ • (z-x)∈Q ∧
          κ*‖euclideanVector (z-x)‖ ≤ |pairDet (z-x) (field hF χ v (x+θ • (z-x)))|) ∧
        (dot (h-g) (field hF χ v z))^2 / pairCurvature x z g h ≤ C₀ ∧
        ∃lam β : ℝ,0 < lam ∧ field hF χ v z=lam • field hF χ v x+β • (z-x) ∧
          |Real.log lam| ≤ C*pairDecrease x z g ∧
          (pairDecrease x z g ≤ 1 → lam^2 ≤ 1+C'*pairDecrease x z g) := by
  have hσ : 0 < 1-c₂ := sub_pos.mpr hc₂
  obtain ⟨m,χ,v,hχ,N,η,hη,hN,hKN,hLip,hvis,hv,hstruct,hcommon,hlocal⟩ :=
    exists_all_endpoint_field hF hK hlevel hstrict hregular hnoncritical hσ
  obtain ⟨U,Q,hU,hKU,hUQ,hQ,hQN,κ,δ,C,hκ,hδ,hC,hpairs⟩ :=
    structured_all_pair_transport hF hK hN hKN hχ hη hLip hvis hv hstruct hcommon hc₁ hc₂
  obtain ⟨Ns,e,C₀,hNs,hKNs,he,hC₀,hsecant⟩ := PlanarCrossing.compact_uniform_secant hK hlocal
  have hC' : 0 ≤ Real.exp (2*C)-1 := by
    have h := Real.exp_le_exp.mpr (by positivity : (0 : ℝ) ≤ 2*C)
    rw [Real.exp_zero] at h
    linarith
  refine ⟨m,χ,v,hχ,U∩Ns,Q,hU.inter hNs,fun x hx => ⟨hKU hx,hKNs hx⟩,
    (closure_mono inter_subset_left).trans hUQ,hQ,η,κ,min δ e,C,Real.exp (2*C)-1,C₀,
    hη,hκ,lt_min hδ he,hC,hC',hC₀,
    fun x hx => hLip x (hQN hx),fun x hx => hvis x (hQN hx),
    fun x hx => hcommon x (hQN hx),?_⟩
  intro x hx z hz g h hp hs
  have hn := FrameNorms.euclidean_norm_sq (euclideanVector (z-x))
  change ‖euclideanVector (z-x)‖^2=sqNorm (z-x) at hn
  have hsmall : ‖z-x‖ < min δ e :=
    (norm_le_of_sqNorm_le (norm_nonneg _) hn.symm.le).trans_lt hs
  obtain ⟨ht,lam,β,hlam,hend,hlog⟩ := hpairs x hx.1 z hz.1 g h hp
    (hsmall.trans_le (min_le_left _ _))
  have hsec := hsecant x hx.2 z (hsmall.le.trans (min_le_right _ _))
  have hcurv : 0 < pairCurvature x z g h :=
    (mul_pos hσ hp.decrease_pos).trans_le hp.curvature
  have hgd : dot g (z-x)= -pairDecrease x z g := by simp only [pairDecrease,pairStep,neg_neg]
  exact ⟨ht,hsec g h hp.gradient_x hp.gradient_z _ _ hp.decrease_pos.le hcurv hgd rfl hp.curvature,
    lam,β,hlam,hend,hlog,fun hd => square_bound_of_log_bound hlam hp.decrease_pos.le hd hlog⟩

end BfgsVerification.PlanarAllPairs
