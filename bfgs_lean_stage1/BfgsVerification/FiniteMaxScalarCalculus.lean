import BfgsVerification.PoweredGaugeProfiles
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter
namespace BfgsVerification.FiniteMaxRadial

def maximum {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (f : ι → ℝ → ℝ) (x : ℝ) :=
  s.sup' hne (fun i => f i x)

theorem maximum_eq_common {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f : ι → ℝ → ℝ} {x c : ℝ} (hv : ∀ i ∈ s, f i x = c) : maximum s hne f x = c :=
  Finset.sup'_eq_of_forall hne (fun i => f i x) hv

/-- A finite maximum has the common actual derivative when all its values and
first derivatives agree at the point. The proof permits infinitely many local
changes of the maximizing index. -/
theorem maximum_hasDerivAt_common {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f : ι → ℝ → ℝ} {x c d : ℝ} (hv : ∀ i ∈ s, f i x = c)
    (hd : ∀ i ∈ s, HasDerivAt (f i) d x) : HasDerivAt (maximum s hne f) d x := by
  have hlim (i : ι) (hi : i ∈ s) :
      Tendsto (fun z => ‖z-x‖⁻¹*‖f i z-c-(z-x)*d‖) (𝓝 x) (𝓝 0) := by
    simpa only [hv i hi,smul_eq_mul] using (hasDerivAt_iff_tendsto.mp (hd i hi))
  have hsum : Tendsto (fun z => ∑ i ∈ s, ‖z-x‖⁻¹*‖f i z-c-(z-x)*d‖) (𝓝 x) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum s hlim
  apply hasDerivAt_iff_tendsto.mpr
  rw [maximum_eq_common hne hv]
  simp only [smul_eq_mul]
  apply squeeze_zero (fun _ => by positivity) _ hsum
  intro z
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' hne (fun i => f i z)
  have he' : maximum s hne f z = f i z := he
  rw [he']
  exact Finset.single_le_sum (f := fun j => ‖z-x‖⁻¹*‖f j z-c-(z-x)*d‖)
    (fun j _ => by positivity) hi

def activeIndices {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (x : ℝ) : Finset ι := s.filter (fun i => f i x = maximum s hne f x)

theorem activeIndices_nonempty {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (x : ℝ) : (activeIndices s hne f x).Nonempty := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' hne (fun i => f i x)
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,he.symm⟩⟩

/-- The nearby maximizers belong to the actual active set at the center;
finiteness removes inactive value gaps without any switching-count premise. -/
theorem maximum_eventually_eq_active {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f : ι → ℝ → ℝ} {x : ℝ} (hc : ∀ i ∈ s, ContinuousAt (f i) x) :
    maximum s hne f =ᶠ[𝓝 x]
      maximum (activeIndices s hne f x) (activeIndices_nonempty s hne f x) f := by
  classical
  obtain ⟨i₀,hi₀⟩ := activeIndices_nonempty s hne f x
  have hi₀s := (Finset.mem_filter.mp hi₀).1
  have hi₀a := (Finset.mem_filter.mp hi₀).2
  have hdom : ∀ᶠ z in 𝓝 x, ∀ i ∈ s, i ∉ activeIndices s hne f x → f i z < f i₀ z := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    by_cases ha : i ∈ activeIndices s hne f x
    · exact Eventually.of_forall (fun _ h => (h ha).elim)
    have hneq : f i x ≠ maximum s hne f x := fun he => ha (Finset.mem_filter.mpr ⟨hi,he⟩)
    have hgap : f i x < f i₀ x := by
      rw [hi₀a]
      exact lt_of_le_of_ne (Finset.le_sup' (fun i => f i x) hi) hneq
    exact ((hc i hi).eventually_lt (hc i₀ hi₀s) hgap).mono (fun _ hz _ => hz)
  filter_upwards [hdom] with z hz
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    by_cases ha : i ∈ activeIndices s hne f x
    · exact Finset.le_sup' (fun i => f i z) ha
    · exact (hz i hi ha).le.trans (Finset.le_sup' (fun i => f i z) hi₀)
  · apply Finset.sup'_le
    intro i hi
    exact Finset.le_sup' (fun i => f i z) (Finset.mem_filter.mp hi).1

theorem maximum_hasDerivAt_of_active_agreement {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f : ι → ℝ → ℝ} {x D : ℝ} {d : ι → ℝ}
    (hd : ∀ i ∈ s, HasDerivAt (f i) (d i) x)
    (heq : ∀ i ∈ s, f i x = maximum s hne f x → d i = D) :
    HasDerivAt (maximum s hne f) D x := by
  have ha : ∀ i ∈ activeIndices s hne f x, f i x = maximum s hne f x :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have hda : ∀ i ∈ activeIndices s hne f x, HasDerivAt (f i) D x := by
    intro i hi
    have his := (Finset.mem_filter.mp hi).1
    rw [← heq i his (ha i hi)]
    exact hd i his
  exact (maximum_hasDerivAt_common (activeIndices_nonempty s hne f x) ha hda).congr_of_eventuallyEq
    (maximum_eventually_eq_active hne (fun i hi => (hd i hi).continuousAt))

theorem maximum_deriv_eq_active {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f d : ι → ℝ → ℝ} {U : Set ℝ}
    (hd : ∀ i ∈ s, ∀ x ∈ U, HasDerivAt (f i) (d i x) x)
    (ha : ∀ x ∈ U, ∀ i ∈ s, ∀ j ∈ s,
      f i x = maximum s hne f x → f j x = maximum s hne f x → d i x = d j x)
    {x : ℝ} (hx : x ∈ U) {i : ι} (hi : i ∈ s) (hia : f i x = maximum s hne f x) :
    deriv (maximum s hne f) x = d i x :=
  (maximum_hasDerivAt_of_active_agreement hne (fun j hj => hd j hj x hx)
    (fun j hj hja => ha x hx j hj i hi hja hia)).deriv

theorem maximum_deriv_centered_bound {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f d : ι → ℝ → ℝ} {U : Set ℝ} {L : ℝ≥0}
    (hd : ∀ i ∈ s, ∀ x ∈ U, HasDerivAt (f i) (d i x) x)
    (ha : ∀ x ∈ U, ∀ i ∈ s, ∀ j ∈ s,
      f i x = maximum s hne f x → f j x = maximum s hne f x → d i x = d j x)
    (hLip : ∀ i ∈ s, LipschitzOnWith L (d i) U) {x : ℝ} (hx : x ∈ U) :
    ∀ᶠ z in 𝓝 x, z ∈ U → ‖deriv (maximum s hne f) z-deriv (maximum s hne f) x‖ ≤
      L*‖z-x‖ := by
  have heq := maximum_eventually_eq_active hne (fun i hi => (hd i hi x hx).continuousAt)
  filter_upwards [heq] with z hz
  intro hzU
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' (activeIndices_nonempty s hne f x) (fun i => f i z)
  have his := (Finset.mem_filter.mp hi).1
  have hia := (Finset.mem_filter.mp hi).2
  have hiz : f i z = maximum s hne f z := by rw [hz]; exact he.symm
  rw [maximum_deriv_eq_active hne hd ha hzU his hiz,maximum_deriv_eq_active hne hd ha hx his hia]
  simpa only [dist_eq_norm] using (hLip i his).dist_le_mul z hzU x hx

theorem maximum_deriv_continuousOn {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f d : ι → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {L : ℝ≥0}
    (hd : ∀ i ∈ s, ∀ x ∈ U, HasDerivAt (f i) (d i x) x)
    (ha : ∀ x ∈ U, ∀ i ∈ s, ∀ j ∈ s,
      f i x = maximum s hne f x → f j x = maximum s hne f x → d i x = d j x)
    (hLip : ∀ i ∈ s, LipschitzOnWith L (d i) U) :
    ContinuousOn (deriv (maximum s hne f)) U := by
  intro x hx
  have hb : ∀ᶠ z in 𝓝 x, ‖deriv (maximum s hne f) z-deriv (maximum s hne f) x‖ ≤ L*‖z-x‖ := by
    filter_upwards [maximum_deriv_centered_bound hne hd ha hLip hx,hU.mem_nhds hx] with z hz hzU
    exact hz hzU
  have hlim : Tendsto (fun z : ℝ => (L : ℝ)*‖z-x‖) (𝓝 x) (𝓝 0) := by
    have hh : Continuous (fun z : ℝ => (L : ℝ)*‖z-x‖) := by fun_prop
    simpa using hh.tendsto x
  have hc : ContinuousAt (deriv (maximum s hne f)) x := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb hlim
  exact hc.continuousWithinAt

/-- A uniform centered local slope bound globalizes along a real interval.
This is a Dini mean-value argument, with no piece-count or switching premise. -/
theorem sub_le_of_centered_local_bound {D : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hc : ContinuousOn D U) {L : ℝ}
    (hb : ∀ x ∈ U, ∀ᶠ z in 𝓝 x, z ∈ U → ‖D z-D x‖ ≤ L*‖z-x‖)
    {a b : ℝ} (ha : a ∈ U) (hbU : b ∈ U) (hab : a ≤ b) :
    D b-D a ≤ L*(b-a) := by
  have hsub : Icc a b ⊆ U := hUc.ordConnected.out ha hbU
  have hbound : ∀ x ∈ Ico a b, ∀ r : ℝ, L < r → ∃ᶠ z in 𝓝[>] x, slope D x z < r := by
    intro x hx r hr
    have hxU := hsub ⟨hx.1,hx.2.le⟩
    have he : ∀ᶠ z in 𝓝[>] x, slope D x z < r := by
      filter_upwards [((hb x hxU).and (hU.mem_nhds hxU)).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hz hzx
      have hzbound := hz.1 hz.2
      have hpos : 0 < z-x := sub_pos.mpr hzx
      have hh : D z-D x ≤ L*(z-x) := by
        rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hpos] at hzbound
        exact (le_abs_self _).trans hzbound
      have hs : slope D x z ≤ L := by
        rw [slope_def_field]
        exact (div_le_iff₀ hpos).mpr hh
      exact hs.trans_lt hr
    exact he.frequently
  have hBD : ∀ x ∈ Ico a b, HasDerivWithinAt (fun t => D a+L*(t-a)) L (Ici x) x := by
    intro x hx
    have hd := (((hasDerivAt_id x).sub_const a).const_mul L).const_add (D a)
    simpa using hd.hasDerivWithinAt
  have hv := image_le_of_liminf_slope_right_le_deriv_boundary (hc.mono hsub)
    (show D a ≤ D a+L*(a-a) by simp)
    (show ContinuousOn (fun t => D a+L*(t-a)) (Icc a b) by fun_prop)
    hBD hbound (show b ∈ Icc a b from ⟨hab,le_rfl⟩)
  linarith

theorem norm_sub_le_of_centered_local_bound {D : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hc : ContinuousOn D U) {L : ℝ}
    (hb : ∀ x ∈ U, ∀ᶠ z in 𝓝 x, z ∈ U → ‖D z-D x‖ ≤ L*‖z-x‖)
    {a b : ℝ} (ha : a ∈ U) (hbU : b ∈ U) : ‖D b-D a‖ ≤ L*‖b-a‖ := by
  wlog hab : a ≤ b generalizing a b
  · have hba := this hbU ha (le_of_not_ge hab)
    simpa only [norm_sub_rev] using hba
  have hup := sub_le_of_centered_local_bound hU hUc hc hb ha hbU hab
  have hlo := sub_le_of_centered_local_bound hU hUc hc.neg
    (fun x hx => (hb x hx).mono (fun z hz hzU => by simpa only [neg_sub_neg,norm_sub_rev] using hz hzU))
    ha hbU hab
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),abs_le]
  constructor <;> linarith

theorem maximum_deriv_lipschitzOn {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {f d : ι → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U) {L : ℝ≥0}
    (hd : ∀ i ∈ s, ∀ x ∈ U, HasDerivAt (f i) (d i x) x)
    (ha : ∀ x ∈ U, ∀ i ∈ s, ∀ j ∈ s,
      f i x = maximum s hne f x → f j x = maximum s hne f x → d i x = d j x)
    (hLip : ∀ i ∈ s, LipschitzOnWith L (d i) U) :
    LipschitzOnWith L (deriv (maximum s hne f)) U := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  simp only [dist_eq_norm]
  exact norm_sub_le_of_centered_local_bound hU hUc (maximum_deriv_continuousOn hne hU hd ha hLip)
    (fun z hz => maximum_deriv_centered_bound hne hd ha hLip hz) hy hx

end BfgsVerification.FiniteMaxRadial
