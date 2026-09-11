import BfgsVerification.PlanarAllPairTransversality
import BfgsVerification.PlanarCommonPairingBuffer
import BfgsVerification.PlanarEndpointTransport

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Metric
namespace BfgsVerification.PlanarAllPairs
open PlanarCornerCharts PlanarObjectiveField ConvexSubdifferential AffineCriticalObjective
open TransportedCertificate HomogeneousPlanar

/-- One buffered neighborhood and one set of constants work for every close
eligible pair. All intermediate segment points lie in the proved compact
structural buffer. No actual trajectory is part of the statement. -/
theorem structured_all_pair_transport {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {K N : Set (Vec 2)} (hK : IsCompact K) (hN : IsOpen N) (hKN : K⊆N)
    {m : ℕ} {χ : Fin m → Vec 2 → ℝ} {v : Fin m → ℝ → Vec 2}
    (hχ : ∀i,ContDiff ℝ ∞ (χ i)) {η : ℝ} (hη : 0 < η)
    (hLip : ∀x∈N,∃L : ℝ≥0,∃U∈𝓝 x,LipschitzOnWith L (field hF χ v) U)
    (hvis : ∀x∈N,∀g∈subdifferential F x,η ≤ dot g (field hF χ v x))
    (hv : ∀x∈N,∀i,ContDiffAt ℝ 1 (v i) (F x))
    (hstruct : ∀x∈N,ContDiffAt ℝ 2 F x ∨ ∃i,∀ᶠ z in 𝓝 x,field hF χ v z=v i (F z))
    (hcommon : ∀x∈N,∀g∈subdifferential F x,∀h∈subdifferential F x,
      dot g (field hF χ v x)=dot h (field hF χ v x))
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) :
    ∃U Q : Set (Vec 2),IsOpen U ∧ K⊆U ∧ closure U⊆Q ∧ IsCompact Q ∧ Q⊆N ∧
      ∃κ δ C : ℝ,0 < κ ∧ 0 < δ ∧ 0 ≤ C ∧
      ∀x∈U,∀z∈U,∀g h,EligiblePair F c₁ c₂ x z g h → ‖z-x‖ < δ →
        (∀θ∈Icc (0 : ℝ) 1,x+θ • (z-x)∈Q ∧
          κ*‖euclideanVector (z-x)‖ ≤ |pairDet (z-x) (field hF χ v (x+θ • (z-x)))|) ∧
        ∃lam β : ℝ,0 < lam ∧ field hF χ v z=lam • field hF χ v x+β • (z-x) ∧
          |Real.log lam| ≤ C*pairDecrease x z g := by
  obtain ⟨V,Q,hV,hKV,hVQ,hQ,hQN,M,ρ,hρ,G,hG,hballs,hW,hM⟩ :=
    exists_compact_uniform_field_buffer hK hN hKN hLip
  have hcont : ∀p∈N,ContinuousAt (field hF χ v) p := by
    intro p hp
    obtain ⟨L,V,hV,hLV⟩ := hLip p hp
    exact hLV.continuousOn.continuousAt hV
  obtain ⟨A,hA,hvel⟩ := compact_velocity_derivative_bound (convex_continuous hF) hQ
    (fun p hp => hv p (hQN hp))
  obtain ⟨κ,hκ,e,he,htrans⟩ := compact_pair_transversality_length hF hQ hc₂ (field hF χ v)
    (fun p hp => hcont p (hQN hp))
    (fun p hp g hg => hη.trans_le (hvis p (hQN hp) g hg))
    (fun p hp => hcommon p (hQN hp))
  obtain ⟨r,hr,hbuffer⟩ := hK.exists_cthickening_subset_open hV hKV
  let U := thickening (r/2) K
  let δ := min e (r/2)
  let C : ℝ := 2*max (6*(M:ℝ)/(κ*(η/G))) (A/κ)
  have hUQ : closure U⊆Q :=
    (closure_thickening_subset_cthickening (r/2) K).trans
      ((cthickening_mono (by linarith : r/2 ≤ r) K).trans (hbuffer.trans (subset_closure.trans hVQ)))
  have hδ : 0 < δ := lt_min he (half_pos hr)
  have hsegment (x : Vec 2) (hx : x∈U) (s : Vec 2) (hs : ‖s‖ < δ) :
      ∀θ∈Icc (0 : ℝ) 1,x+θ • s∈Q := by
    intro θ hθ
    obtain ⟨p,hp,hxp⟩ := mem_thickening_iff.mp hx
    apply hVQ
    apply subset_closure
    apply hbuffer
    apply thickening_subset_cthickening r K
    apply mem_thickening_iff.mpr
    refine ⟨p,hp,?_⟩
    have hs' : ‖s‖ < r/2 := hs.trans_le (min_le_right _ _)
    calc
      dist (x+θ • s) p ≤ dist (x+θ • s) x+dist x p := dist_triangle _ _ _
      _ < r := by
        rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hθ.1]
        have hmul : θ*‖s‖ ≤ ‖s‖ := mul_le_of_le_one_left (norm_nonneg s) hθ.2
        linarith
  refine ⟨U,Q,isOpen_thickening,self_subset_thickening (half_pos hr) K,hUQ,hQ,hQN,
    κ,δ,C,hκ,hδ,by dsimp [C]; positivity,?_⟩
  intro x hx z hz g h hp hs
  have hxQ := hUQ (subset_closure hx)
  have hzQ := hUQ (subset_closure hz)
  have hsQ := hsegment x hx (z-x) hs
  have ht := htrans x hxQ z hzQ g h hp (hs.trans_le (min_le_left _ _))
  refine ⟨fun θ hθ => ⟨hsQ θ hθ,ht θ hθ⟩,?_⟩
  have hgd : dot g (z-x)= -pairDecrease x z g := by simp only [pairDecrease,pairStep,neg_neg]
  have hdec : F (x+(z-x)) ≤ F x := by
    have ha := hp.armijo
    have hd := mul_pos hc₁ hp.decrease_pos
    have heq : x+(z-x)=z := by abel
    rw [heq]
    linarith
  obtain ⟨lam,β,hlam,hend,hlog⟩ := structured_field_segment_transport hF hχ
    (eligible_step_ne_zero hp) (fun p hp => hv p (hQN hp))
    (fun p hp => hstruct p (hQN hp)) (fun p hp => hcont p (hQN hp))
    hη hG hA.le hκ (fun p hp => hvis p (hQN hp)) hW hM hvel hsQ ht
    hp.gradient_x hp.decrease_pos.le hgd hdec
  refine ⟨lam,β,hlam,?_,hlog⟩
  have heq : x+(z-x)=z := by abel
  rwa [heq] at hend

end BfgsVerification.PlanarAllPairs
