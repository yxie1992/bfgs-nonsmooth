import BfgsVerification.ParabolicExampleSeparation
import BfgsVerification.ParabolicCertificate

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.ParabolicRadialBoundary
open Parabolic TransportedCertificate RadialCertificate

def family : Family 2 where
  a := ![1,2]
  b := ![1,-1]
  a_pos := by intro i; fin_cases i <;> norm_num
  negative_slope := ⟨1,by norm_num⟩
  positive_slope := ⟨0,by norm_num⟩

def objective : Vec 2 → ℝ := family.objective
def base (u : ℝ) : Vec 2 := ![u,u^2/2]
def oldPoint (u ε : ℝ) : Vec 2 := ![u,u^2/2-ε]
def newPoint (u ε : ℝ) : Vec 2 := ![u,u^2/2+ε/2]
def oldGradient (u : ℝ) : Vec 2 := ![4*u,-1]
def newGradient (u : ℝ) : Vec 2 := ![2*u,1]

theorem objective_eq_max (x : Vec 2) :
    objective x = max ((x 0)^2+x 1) (2*(x 0)^2-x 1) := by
  apply le_antisymm
  · change family.objective x ≤ _
    apply Finset.sup'_le
    intro i _
    fin_cases i
    · simpa [family,Family.branch] using le_max_left ((x 0)^2+x 1) (2*(x 0)^2-x 1)
    · simpa [family,Family.branch,sub_eq_add_neg] using le_max_right ((x 0)^2+x 1) (2*(x 0)^2-x 1)
  · apply max_le
    · simpa [objective,family,Family.branch] using family.branch_le 0 x
    · simpa [objective,family,Family.branch,sub_eq_add_neg] using family.branch_le 1 x

theorem upper_value {x : Vec 2} (hx : (x 0)^2/2 ≤ x 1) :
    objective x = (x 0)^2+x 1 := by
  rw [objective_eq_max,max_eq_left (by linarith)]

theorem lower_value {x : Vec 2} (hx : x 1 ≤ (x 0)^2/2) :
    objective x = 2*(x 0)^2-x 1 := by
  rw [objective_eq_max,max_eq_right (by linarith)]

theorem upper_hasGradient {x : Vec 2} (hx : (x 0)^2/2 < x 1) :
    HasFDerivAt objective (gradientFunctional (newGradient (x 0))) x := by
  have he : objective =ᶠ[𝓝 x] family.branch 0 := by
    have hc : Continuous (fun w : Vec 2 => (w 0)^2/2) := by fun_prop
    filter_upwards [(isOpen_lt hc (continuous_apply 1)).mem_nhds hx] with w hw
    rw [upper_value hw.le]
    simp [Family.branch,family]
  convert (family.branch_hasGradient 0 x).congr_of_eventuallyEq he using 1
  simp [Family.branchGradient,family,newGradient]

theorem lower_hasGradient {x : Vec 2} (hx : x 1 < (x 0)^2/2) :
    HasFDerivAt objective (gradientFunctional (oldGradient (x 0))) x := by
  have he : objective =ᶠ[𝓝 x] family.branch 1 := by
    have hc : Continuous (fun w : Vec 2 => (w 0)^2/2) := by fun_prop
    filter_upwards [(isOpen_lt (continuous_apply 1) hc).mem_nhds hx] with w hw
    rw [lower_value hw.le]
    simp [Family.branch,family,sub_eq_add_neg]
  convert (family.branch_hasGradient 1 x).congr_of_eventuallyEq he using 1
  simp [Family.branchGradient,family,oldGradient]
  ring

theorem pair_values {u ε : ℝ} (hε : 0 < ε) :
    objective (oldPoint u ε)=3*u^2/2+ε ∧ objective (newPoint u ε)=3*u^2/2+ε/2 := by
  rw [lower_value (by simp [oldPoint]; linarith),upper_value (by simp [newPoint]; linarith)]
  simp [oldPoint,newPoint]
  constructor <;> ring

theorem pair_gradients {u ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt objective (gradientFunctional (oldGradient u)) (oldPoint u ε) ∧
      HasFDerivAt objective (gradientFunctional (newGradient u)) (newPoint u ε) := by
  constructor
  · exact lower_hasGradient (x := oldPoint u ε) (by simp [oldPoint]; linarith)
  · exact upper_hasGradient (x := newPoint u ε) (by simp [newPoint]; linarith)

theorem pair_curvature (u ε : ℝ) :
    pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u) (newGradient u)=3*ε := by
  simp [pairCurvature,pairStep,oldPoint,newPoint,oldGradient,newGradient,dot,Fin.sum_univ_two]
  ring

theorem radial_numerator (u ε : ℝ) :
    radialNumerator 0 (newPoint u ε) (oldGradient u) (newGradient u) = -u^2+ε := by
  simp [radialNumerator,oldPoint,newPoint,oldGradient,newGradient,dot,Fin.sum_univ_two]
  ring

theorem radial_quotient (u ε : ℝ) :
    (radialNumerator 0 (newPoint u ε) (oldGradient u) (newGradient u))^2 /
      pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u) (newGradient u) =
        (u^2-ε)^2/(3*ε) := by
  rw [radial_numerator,pair_curvature]
  congr 1
  ring

theorem radial_quotient_tendsto {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun ε => (radialNumerator 0 (newPoint u ε) (oldGradient u) (newGradient u))^2 /
      pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u) (newGradient u))
      (𝓝[>] 0) atTop := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hn : Tendsto (fun ε : ℝ => (u^2-ε)^2) (𝓝[>] 0) (𝓝 ((u^2)^2)) := by
    simpa using (tendsto_const_nhds.sub he).pow 2
  have hd : Tendsto (fun ε : ℝ => 3*ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using he.const_mul 3,?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    change 0 < 3*ε
    positivity
  simp_rw [radial_quotient]
  simpa only [div_eq_mul_inv] using
    hn.pos_mul_atTop (sq_pos_of_pos (sq_pos_of_ne_zero hu)) hd.inv_tendsto_nhdsGT_zero

theorem objective_zero : objective 0=0 := family.objective_zero

theorem objective_convex : ConvexOn ℝ univ objective := family.objective_convex

theorem unique_minimizer : (∀ x, 0 ≤ objective x) ∧ (∀ x, objective x=0 → x=0) :=
  ⟨family.objective_nonneg,family.unique_zero⟩

theorem sublevel_compact (a : ℝ) : IsCompact {x | objective x ≤ a} := family.sublevel_compact a

theorem active_tie (u : ℝ) : family.Active 0 (base u) ∧ family.Active 1 (base u) := by
  have hv : objective (base u) = 3*u^2/2 := by
    rw [upper_value (by simp [base])]
    simp [base]
    ring
  constructor <;> change objective (base u) = _
  <;> rw [hv]
  <;> simp [Family.branch,family,base]
  <;> ring

theorem active_radial_jump (u : ℝ) :
    newGradient u-oldGradient u = ![-2*u,2] ∧
      dot (newGradient u-oldGradient u) (base u) = -u^2 := by
  constructor
  · ext i
    fin_cases i <;> simp [newGradient,oldGradient] <;> ring
  · simp [newGradient,oldGradient,base,dot,Fin.sum_univ_two]
    ring

theorem pair_points_tendsto (u : ℝ) :
    Tendsto (oldPoint u) (𝓝[>] 0) (𝓝 (base u)) ∧
      Tendsto (newPoint u) (𝓝[>] 0) (𝓝 (base u)) := by
  have ho : Continuous (oldPoint u) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [oldPoint] <;> fun_prop
  have hn : Continuous (newPoint u) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [newPoint] <;> fun_prop
  exact ⟨by simpa [oldPoint,base] using (ho.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds,
    by simpa [newPoint,base] using (hn.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds⟩

theorem exists_nonzero_base {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    ∃ u : ℝ, u ≠ 0 ∧ K ∈ 𝓝 (base u) := by
  obtain ⟨O,hOK,hO,hzero⟩ := mem_nhds_iff.mp hK
  have hc : Continuous base := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [base] <;> fun_prop
  have ht : Tendsto base (𝓝[>] 0) (𝓝 (0 : Vec 2)) := by
    have he : base 0 = 0 := by ext i; fin_cases i <;> norm_num [base]
    rw [← he]
    exact (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hp : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  obtain ⟨u,hu,hOu⟩ := (hp.and (ht.eventually (hO.mem_nhds hzero))).exists
  exact ⟨u,hu.ne',mem_of_superset (hO.mem_nhds hOu) hOK⟩

/-- The positive band is fixed before every candidate radial bound; all
endpoints, values and derivatives come from the literal two-piece objective. -/
theorem unbounded_radial_pairs {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    ∃ η : ℝ, 0 < η ∧ ∀ C : ℝ, ∃ x z g h : Vec 2,
      x ∈ K ∧ z ∈ K ∧ η ≤ objective z ∧ objective z ≤ objective x ∧
      HasFDerivAt objective (gradientFunctional g) x ∧
      HasFDerivAt objective (gradientFunctional h) z ∧
      0 < secantCurvature x z g h ∧
      C*secantCurvature x z g h < (radialNumerator 0 z g h)^2 := by
  obtain ⟨u,hu,hKu⟩ := exists_nonzero_base hK
  refine ⟨u^2,sq_pos_of_ne_zero hu,?_⟩
  intro C
  have hr := (radial_quotient_tendsto hu).eventually (eventually_gt_atTop C)
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hx,hz,hq⟩ := (hp.and (((pair_points_tendsto u).1.eventually hKu).and
    (((pair_points_tendsto u).2.eventually hKu).and hr))).exists
  obtain ⟨hFx,hFz⟩ := pair_values (u := u) hε
  obtain ⟨hg,hh⟩ := pair_gradients (u := u) hε
  have ht : 0 < pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u) (newGradient u) := by
    rw [pair_curvature]
    positivity
  refine ⟨oldPoint u ε,newPoint u ε,oldGradient u,newGradient u,hx,hz,?_,?_,hg,hh,ht,?_⟩
  · rw [hFz]
    nlinarith [sq_nonneg u]
  · rw [hFx,hFz]
    linarith
  · exact (lt_div_iff₀ ht).mp hq

theorem not_radial_secant_on_neighborhood {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    ¬ HasRadialSecantBounds objective K 0 := by
  intro hrs
  obtain ⟨η,hη,hex⟩ := unbounded_radial_pairs hK
  obtain ⟨C,hC⟩ := hrs η hη
  obtain ⟨x,z,g,h,hx,hz,hband,horder,hg,hh,ht,hexcess⟩ := hex C
  have hb := hC x z g h hx hz (by simpa only [objective_zero,zero_add] using hband) horder hg hh ht
  exact not_lt_of_ge hb hexcess

theorem not_radial_secant_on_sublevel {B : ℝ} (hB : 0 < B) :
    ¬ HasRadialSecantBounds objective {x | objective x ≤ B} 0 := by
  apply not_radial_secant_on_neighborhood
  have hO : IsOpen {x | objective x < B} := isOpen_lt family.objective_continuous continuous_const
  exact mem_of_superset (hO.mem_nhds (by change objective 0 < B; rwa [objective_zero]))
    (fun x hx => (show objective x < B from hx).le)

/-- Module Q's already verified actual-run theorem applies to this literal
family too: failure of the old radial criterion is compatible with convergence. -/
theorem converges_without_radial_secant {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    (∀ R : AdmissibleBFGSRun 2 objective,
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ¬ HasRadialSecantBounds objective K 0 :=
  ⟨fun R => R.parabolic_convergence family,not_radial_secant_on_neighborhood hK⟩

end BfgsVerification.ParabolicRadialBoundary
