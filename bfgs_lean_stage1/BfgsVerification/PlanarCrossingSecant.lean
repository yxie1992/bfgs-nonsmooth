import BfgsVerification.PlanarPairControl

/-! The actual two-branch crossing estimate, including actual accepted endpoint
derivatives and the tie point selected by the intermediate value theorem. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification
namespace PlanarCrossing
open PlanarCornerCharts ConvexSubdifferential HomogeneousPlanar

/-- A planar coordinate-norm Cauchy estimate with an explicit conversion
constant; no Euclidean and finite-Pi norms are identified. -/
theorem abs_dot_le_four_pi_norm (u v : Vec 2) : |dot u v|≤4*‖u‖*‖v‖ := by
  calc
    _≤‖euclideanVector u‖*‖euclideanVector v‖ := abs_dot_le_euclidean_norm u v
    _≤(2*‖u‖)*(2*‖v‖) := by
      gcongr
      · exact euclidean_norm_le_two_pi_norm u
      · exact euclidean_norm_le_two_pi_norm v
    _=_ := by ring

theorem crossing_step_bound {a b s r : Vec 2} {A L d t : ℝ}
    (hA : 0≤A) (hL : 0≤L) (hd : 0≤d) (ht : 0≤t)
    (hpair : ∀ v, ‖v‖≤A*(|dot a v|+|dot b v|))
    (ha : dot a s = -d) (hb : dot b s=t-d-dot r s)
    (hr : ‖r‖≤L*‖s‖) : ‖s‖≤A*(2*d+t+4*L*‖s‖^2) := by
  have hrem : |dot r s|≤4*L*‖s‖^2 := by
    calc
      _≤4*‖r‖*‖s‖ := abs_dot_le_four_pi_norm r s
      _≤4*(L*‖s‖)*‖s‖ := by gcongr
      _=_ := by ring
  have hbs : |dot b s|≤t+d+4*L*‖s‖^2 := by
    rw [hb]
    calc
      _≤|t-d|+|dot r s| := abs_sub _ _
      _≤(|t|+|d|)+|dot r s| := by gcongr; exact abs_sub _ _
      _≤t+d+4*L*‖s‖^2 := by rw [abs_of_nonneg ht,abs_of_nonneg hd]; gcongr
  calc
    _≤A*(|dot a s|+|dot b s|) := hpair s
    _≤A*(d+(t+d+4*L*‖s‖^2)) := by
      rw [ha,abs_neg,abs_of_nonneg hd]
      gcongr
    _=_ := by ring

set_option maxHeartbeats 800000 in
/-- This local bound contains all of the actual objective and gradient bridges.
Its geometric constants are supplied later from the source's local C² charts. -/
theorem actual_crossing_secant_bound {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {f : Fin 2 → Vec 2 → ℝ} {W : Vec 2 → Vec 2} {V : Set (Vec 2)}
    (hV : Convex ℝ V) (hrep : ∀ x ∈ V, LocalFiniteMax F f x)
    (hdiff : ∀ i, ∀ x ∈ V, DifferentiableAt ℝ (f i) x)
    {L G H B A σ : ℝ} (hL : 0≤L) (hG : 0≤G) (hH : 0≤H) (hB : 0≤B)
    (hA : 0<A) (hσ : 0<σ)
    (hgradLip : ∀ i, ∀ x ∈ V, ∀ z ∈ V,
      ‖coordinateGradient (f i) z-coordinateGradient (f i) x‖≤L*‖z-x‖)
    (hWBound : ∀ x ∈ V, ‖W x‖≤G)
    (hgradBound : ∀ i, ∀ x ∈ V, ‖coordinateGradient (f i) x‖≤H)
    (hWLip : ∀ x ∈ V, ∀ z ∈ V, ‖W z-W x‖≤B*‖z-x‖)
    (hcommon : ∀ p ∈ V, ∀ g ∈ subdifferential F p, ∀ h ∈ subdifferential F p,
      dot g (W p)=dot h (W p))
    (hpair : ∀ x ∈ V, ∀ v,
      ‖v‖≤A*(|dot (coordinateGradient (f 0) x) v|+|dot (coordinateGradient (f 1) x) v|))
    {x z g h : Vec 2} (hx : x∈V) (hz : z∈V)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z)
    {i j : Fin 2} (hij : i≠j) (hi : f i x=F x) (hj : f j z=F z)
    {d t : ℝ} (hd : 0≤d) (ht : 0<t) (hdescent : dot g (z-x) = -d)
    (hcurv : t=dot (h-g) (z-x)) (hwolfe : σ*d≤t)
    (hsmall : A*(4*L)*‖z-x‖≤1/2) :
    (dot (h-g) (W z))^2/t ≤ (8*(L*G+H*B))^2*(2*A*(1+2/σ))*‖z-x‖ := by
  have hgi := actual_gradient_eq_active_branch hF (hrep x hx) (fun k => hdiff k x hx) hg hi
  have hgj := actual_gradient_eq_active_branch hF (hrep z hz) (fun k => hdiff k z hz) hh hj
  have hseg : segment ℝ x z ⊆ V := hV.segment_subset hx hz
  have hci : ContinuousOn (f i) (segment ℝ x z) :=
    fun p hp => (hdiff i p (hseg hp)).continuousAt.continuousWithinAt
  have hcj : ContinuousOn (f j) (segment ℝ x z) :=
    fun p hp => (hdiff j p (hseg hp)).continuousAt.continuousWithinAt
  have hix : f j x≤f i x := by rw [hi]; exact (hrep x hx).self_of_nhds.2 (mem_range_self j)
  have hjz : f i z≤f j z := by rw [hj]; exact (hrep z hz).self_of_nhds.2 (mem_range_self i)
  obtain ⟨p,hp,htie⟩ := exists_tie_on_segment (F := F) hci hcj hix hjz
  have hpV := hseg hp
  have hpi : f i p=F p := by
    obtain ⟨k,hk⟩ := (hrep p hpV).self_of_nhds.1
    have hkij : k=i ∨ k=j := by omega
    rcases hkij with rfl | rfl
    · exact hk
    · exact htie.trans hk
  have hpj : f j p=F p := htie.symm.trans hpi
  have hsupp (k : Fin 2) (hk : f k p=F p) : coordinateGradient (f k) p∈subdifferential F p :=
    active_gradient_supports hF (hrep p hpV)
      (fun l => hasFDerivAt_coordinateGradient (hdiff l p hpV)) (mem_activeIndices.mpr hk)
  have horth : dot (coordinateGradient (f j) p-coordinateGradient (f i) p) (W p)=0 := by
    rw [dot_sub_left,hcommon p hpV _ (hsupp j hpj) _ (hsupp i hpi),sub_self]
  have hpdist := segment_sub_norm_le hp
  have hiLip : ‖euclideanVector (coordinateGradient (f i) p-g)‖≤(2*L)*‖z-x‖ := by
    rw [← hgi]
    calc
      _≤2*‖coordinateGradient (f i) p-coordinateGradient (f i) x‖ := euclidean_norm_le_two_pi_norm _
      _≤2*(L*‖p-x‖) := by gcongr; exact hgradLip i x hx p hpV
      _≤(2*L)*‖z-x‖ := by nlinarith [mul_le_mul_of_nonneg_left hpdist.1 hL]
  have hjLip : ‖euclideanVector (h-coordinateGradient (f j) p)‖≤(2*L)*‖z-x‖ := by
    rw [← hgj]
    calc
      _≤2*‖coordinateGradient (f j) z-coordinateGradient (f j) p‖ := euclidean_norm_le_two_pi_norm _
      _≤2*(L*‖z-p‖) := by gcongr; exact hgradLip j p hpV z hz
      _≤(2*L)*‖z-x‖ := by nlinarith [mul_le_mul_of_nonneg_left hpdist.2 hL]
  have hjump : ‖euclideanVector (coordinateGradient (f j) p-coordinateGradient (f i) p)‖≤4*H := by
    calc
      _≤2*‖coordinateGradient (f j) p-coordinateGradient (f i) p‖ := euclidean_norm_le_two_pi_norm _
      _≤2*(‖coordinateGradient (f j) p‖+‖coordinateGradient (f i) p‖) := by gcongr; exact norm_sub_le _ _
      _≤4*H := by linarith [hgradBound i p hpV,hgradBound j p hpV]
  have hwp : ‖euclideanVector (W z-W p)‖≤(2*B)*‖z-x‖ := by
    calc
      _≤2*‖W z-W p‖ := euclidean_norm_le_two_pi_norm _
      _≤2*(B*‖z-p‖) := by gcongr; exact hWLip p hpV z hz
      _≤(2*B)*‖z-x‖ := by nlinarith [mul_le_mul_of_nonneg_left hpdist.2 hB]
  have hwz : ‖euclideanVector (W z)‖≤2*G :=
    (euclidean_norm_le_two_pi_norm _).trans (by gcongr; exact hWBound z hz)
  have hnum : |dot (h-g) (W z)|≤(8*(L*G+H*B))*‖z-x‖ := by
    have hb := crossing_numerator_bound (by positivity : 0≤2*L) (by positivity : 0≤2*G)
      (by positivity : 0≤4*H) (by positivity : 0≤2*B) (norm_nonneg (z-x))
      (show h-g=(h-coordinateGradient (f j) p)+
        (coordinateGradient (f j) p-coordinateGradient (f i) p)+(coordinateGradient (f i) p-g) by abel)
      horth hiLip hjLip hwz hjump hwp
    convert hb using 1 <;> ring
  have hpairij : ∀ v, ‖v‖≤A*(|dot (coordinateGradient (f i) x) v|+|dot (coordinateGradient (f j) x) v|) := by
    intro v
    by_cases hi0 : i=0
    · subst i
      have hj1 : j=1 := by omega
      subst j
      exact hpair x hx v
    · have hi1 : i=1 := by omega
      subst i
      have hj0 : j=0 := by omega
      subst j
      simpa only [add_comm] using hpair x hx v
  have ha : dot (coordinateGradient (f i) x) (z-x) = -d := by rwa [hgi]
  have hb : dot (coordinateGradient (f j) x) (z-x)=t-d-
      dot (coordinateGradient (f j) z-coordinateGradient (f j) x) (z-x) := by
    rw [hcurv,hgj,dot_sub_left,dot_sub_left,hdescent]
    ring
  have hstep := crossing_step_bound hA.le hL hd ht.le hpairij ha hb (hgradLip j x hx z hz)
  have hlinear := crossing_linear_curvature (norm_nonneg (z-x)) hA hσ hstep hsmall hwolfe
  exact crossing_secant_correction (by positivity) (by positivity) (norm_nonneg _) ht hnum hlinear

end PlanarCrossing
end BfgsVerification
