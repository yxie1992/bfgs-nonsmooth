import BfgsVerification.PlanarAllPairTransport
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Metric
namespace BfgsVerification.PlanarAllPairs
open PlanarCornerCharts PlanarObjectiveField ConvexSubdifferential AffineCriticalObjective
open TransportedCertificate HomogeneousPlanar

/-- The source's linear squared transport factor follows from its logarithmic
bound, uniformly for predicted decreases in the fixed interval `[0,1]`. -/
theorem square_bound_of_log_bound {lam C d : ℝ} (hlam : 0 < lam)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hlog : |Real.log lam| ≤ C*d) :
    lam^2 ≤ 1+(Real.exp (2*C)-1)*d := by
  have hlog' : 2*Real.log lam ≤ 2*C*d := by
    have hl := (le_abs_self (Real.log lam)).trans hlog
    linarith
  have he : Real.exp (2*C*d) ≤ (1-d)*Real.exp 0+d*Real.exp (2*C) := by
    have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (2*C))
      (sub_nonneg.mpr hd1) hd (by ring : (1-d)+d=1)
    simpa only [smul_eq_mul,mul_zero,zero_add,mul_comm d] using h
  calc
    lam^2 = Real.exp (2*Real.log lam) := by rw [two_mul,Real.exp_add,Real.exp_log hlam,pow_two]
    _ ≤ Real.exp (2*C*d) := Real.exp_le_exp.mpr hlog'
    _ ≤ (1-d)*Real.exp 0+d*Real.exp (2*C) := he
    _ = 1+(Real.exp (2*C)-1)*d := by rw [Real.exp_zero]; ring

/-- Literal Module C all-eligible-pair transversality and transport, derived
from the actual convex objective and its original two-branch regularity. The
field, neighborhoods, compact buffer and constants are constructed before all
eligible endpoint pairs. No trajectory, common metric, or all-pair estimate is
an input. -/
theorem source_all_pair_transport {F : Vec 2 → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec 2)} {ℓ : ℝ}
    (hK : IsCompact K) (hlevel : ∀x∈K,F x=ℓ)
    (hstrict : ∀x y : Vec 2,segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x=y)
    (hregular : ∀x∈K,ContDiffAt ℝ 2 F x ∨ ConvexTwoBranchRegularAt F x)
    (hnoncritical : ∀x∈K,¬IsAffineCritical F x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) :
    ∃m : ℕ,∃χ : Fin m → Vec 2 → ℝ,∃v : Fin m → ℝ → Vec 2,
      (∀i,ContDiff ℝ ∞ (χ i)) ∧ ∃U Q : Set (Vec 2),
      IsOpen U ∧ K⊆U ∧ closure U⊆Q ∧ IsCompact Q ∧
      ∃η κ δ C C' : ℝ,0 < η ∧ 0 < κ ∧ 0 < δ ∧ 0 ≤ C ∧ 0 ≤ C' ∧
      (∀x∈Q,∃L : ℝ≥0,∃V∈𝓝 x,LipschitzOnWith L (field hF χ v) V) ∧
      (∀x∈Q,∀g∈subdifferential F x,η ≤ dot g (field hF χ v x)) ∧
      (∀x∈Q,∀g∈subdifferential F x,∀h∈subdifferential F x,
        dot g (field hF χ v x)=dot h (field hF χ v x)) ∧
      ∀x∈U,∀z∈U,∀g h,EligiblePair F c₁ c₂ x z g h → ‖euclideanVector (z-x)‖ < δ →
        (∀θ∈Icc (0 : ℝ) 1,x+θ • (z-x)∈Q ∧
          κ*‖euclideanVector (z-x)‖ ≤ |pairDet (z-x) (field hF χ v (x+θ • (z-x)))|) ∧
        ∃lam β : ℝ,0 < lam ∧ field hF χ v z=lam • field hF χ v x+β • (z-x) ∧
          |Real.log lam| ≤ C*pairDecrease x z g ∧
          (pairDecrease x z g ≤ 1 → lam^2 ≤ 1+C'*pairDecrease x z g) := by
  obtain ⟨m,χ,v,hχ,N,η,hη,hN,hKN,hLip,hvis,hv,hstruct,hcommon⟩ :=
    exists_pairwise_structured_field hF hK hlevel hstrict hregular hnoncritical
  obtain ⟨U,Q,hU,hKU,hUQ,hQ,hQN,κ,δ,C,hκ,hδ,hC,hpairs⟩ :=
    structured_all_pair_transport hF hK hN hKN hχ hη hLip hvis hv hstruct hcommon hc₁ hc₂
  have hC' : 0 ≤ Real.exp (2*C)-1 := by
    have h := Real.exp_le_exp.mpr (by positivity : (0 : ℝ) ≤ 2*C)
    rw [Real.exp_zero] at h
    linarith
  refine ⟨m,χ,v,hχ,U,Q,hU,hKU,hUQ,hQ,η,κ,δ,C,Real.exp (2*C)-1,
    hη,hκ,hδ,hC,hC',fun x hx => hLip x (hQN hx),fun x hx => hvis x (hQN hx),
    fun x hx => hcommon x (hQN hx),?_⟩
  intro x hx z hz g h hp hs
  have hn := FrameNorms.euclidean_norm_sq (euclideanVector (z-x))
  change ‖euclideanVector (z-x)‖^2=sqNorm (z-x) at hn
  have hs' : ‖z-x‖ < δ :=
    (norm_le_of_sqNorm_le (norm_nonneg _) hn.symm.le).trans_lt hs
  obtain ⟨ht,lam,β,hlam,hend,hlog⟩ := hpairs x hx z hz g h hp hs' 
  exact ⟨ht,lam,β,hlam,hend,hlog,fun hd => square_bound_of_log_bound hlam hp.decrease_pos.le hd hlog⟩

end BfgsVerification.PlanarAllPairs
