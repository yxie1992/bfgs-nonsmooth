import BfgsVerification.PlanarQuadraticCoefficients

/-! The printed square-root tie curve, actual activity, and its radial jump. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.PlanarQuadraticExample

def tieHeight (u : ℝ) : ℝ := (-1+Real.sqrt (1+4*u+2*u^2))/2
def base (u : ℝ) : Vec 2 := ![u,tieHeight u]

theorem tieHeight_continuous : Continuous tieHeight := by
  unfold tieHeight
  fun_prop

theorem tieHeight_zero : tieHeight 0=0 := by norm_num [tieHeight]

theorem tieHeight_equation {u : ℝ} (hu : 0≤u) :
    tieHeight u+(tieHeight u)^2=u+u^2/2 := by
  have hs := Real.sq_sqrt (show 0≤1+4*u+2*u^2 by positivity)
  unfold tieHeight
  nlinarith

theorem tieHeight_pos {u : ℝ} (hu : 0<u) : 0<tieHeight u := by
  have hs := Real.sq_sqrt (show 0≤1+4*u+2*u^2 by positivity)
  have hn := Real.sqrt_nonneg (1+4*u+2*u^2)
  have hlt : 1<Real.sqrt (1+4*u+2*u^2) := by nlinarith
  dsimp [tieHeight]
  linarith

theorem tieHeight_bounds {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    3*u/4<tieHeight u ∧ tieHeight u<u := by
  have hv := tieHeight_pos hu
  have he := tieHeight_equation hu.le
  constructor
  · by_contra h
    push_neg at h
    have hp := mul_nonneg (sub_nonneg.mpr h) (by linarith : 0≤3*u/4+tieHeight u+1)
    have hu2 : u^2<4*u := by nlinarith [mul_pos hu (show 0<4-u by linarith)]
    nlinarith
  · by_contra h
    push_neg at h
    have hp := mul_nonneg (sub_nonneg.mpr h) (by linarith : 0≤tieHeight u+u+1)
    nlinarith [sq_pos_of_pos hu]

theorem tie_branch_values {u : ℝ} (hu : 0≤u) : branch 0 (base u)=branch 1 (base u) := by
  have he := tieHeight_equation hu
  simp only [branch,base,Matrix.cons_val_zero,Matrix.cons_val_one]
  nlinarith

theorem third_inactive_on_tie {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    branch 2 (base u)<branch 0 (base u) := by
  have hv := tieHeight_pos hu
  have hvu := (tieHeight_bounds hu hsmall).2
  have hs : (tieHeight u)^2<u^2 := by
    nlinarith [mul_pos (sub_pos.mpr hvu) (show 0<u+tieHeight u by linarith)]
  have hh : u^2<2*u := by nlinarith [mul_pos hu (show 0<2-u by linarith)]
  change -u-tieHeight u+3*u^2/2+(tieHeight u)^2 < u+u^2+(tieHeight u)^2/2
  nlinarith

theorem tie_active {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    branch 0 (base u)=objective (base u) ∧ branch 1 (base u)=objective (base u) ∧
      branch 2 (base u)<objective (base u) := by
  have ht := tie_branch_values hu.le
  have h2 := third_inactive_on_tie hu hsmall
  have he : objective (base u)=branch 0 (base u) := by
    rw [objective,← ht,max_eq_left h2.le,max_self]
  rw [he]
  exact ⟨rfl,ht.symm,h2⟩

theorem tie_radial_jump {u : ℝ} (hu : 0≤u) :
    gradient 0 (base u)-gradient 1 (base u)=![1+u,-1-2*tieHeight u] ∧
    dot (gradient 0 (base u)-gradient 1 (base u)) (base u)=u^2/2-(tieHeight u)^2 := by
  rw [(gradient_coordinates (base u)).1,(gradient_coordinates (base u)).2.1]
  constructor
  · ext i; fin_cases i <;> simp [base] <;> ring
  · have he := tieHeight_equation hu
    simp only [base,dot,Fin.sum_univ_two,Pi.sub_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
    nlinarith

theorem tie_radial_jump_neg {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    u^2/2-(tieHeight u)^2<0 := by
  have hv := (tieHeight_bounds hu hsmall).1
  have hvpos := tieHeight_pos hu
  have hs := mul_pos (sub_pos.mpr hv) (show 0<tieHeight u+3*u/4 by linarith)
  nlinarith [sq_pos_of_pos hu]

theorem base_continuous : Continuous base := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun u : ℝ => u)
    exact continuous_id
  · exact tieHeight_continuous

theorem base_zero : base 0=0 := by ext i; fin_cases i <;> simp [base,tieHeight_zero]

theorem exists_positive_tie_base {K : Set (Vec 2)} (hK : K∈𝓝 (0 : Vec 2)) :
    ∃ u : ℝ, 0<u ∧ u<1/10 ∧ K∈𝓝 (base u) := by
  obtain ⟨O,hOK,hO,hzero⟩ := mem_nhds_iff.mp hK
  have ht : Tendsto base (𝓝[>] 0) (𝓝 (0 : Vec 2)) := by
    rw [← base_zero]
    exact (base_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : ∀ᶠ u : ℝ in 𝓝[>] 0, u<1/10 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/10)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ u : ℝ in 𝓝[>] 0, 0<u := self_mem_nhdsWithin
  obtain ⟨u,hu,hsmall,hOu⟩ := (hp.and (hs.and (ht.eventually (hO.mem_nhds hzero)))).exists
  exact ⟨u,hu,hsmall,mem_of_superset (hO.mem_nhds hOu) hOK⟩

/-- The printed second-order expansion has a literal cubic remainder bound on
its positive-side source domain. -/
theorem tieHeight_cubic_remainder {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    |tieHeight u-u+u^2/2|≤u^3 := by
  have hv := tieHeight_pos hu
  have hvu := (tieHeight_bounds hu hsmall).2
  have he := tieHeight_equation hu.le
  have hid : (tieHeight u-u+u^2/2)*(1+u+tieHeight u)=u^2/2*(u+tieHeight u) := by
    nlinarith
  have hd : 0<1+u+tieHeight u := by linarith
  have hr : 0≤tieHeight u-u+u^2/2 := by
    apply nonneg_of_mul_nonneg_left (by rw [hid]; positivity) hd
  rw [abs_of_nonneg hr]
  apply (mul_le_mul_right hd).mp
  rw [hid]
  nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hvu.le),mul_nonneg (sq_nonneg u) (show 0≤u*(u+tieHeight u) by positivity)]

end BfgsVerification.PlanarQuadraticExample
