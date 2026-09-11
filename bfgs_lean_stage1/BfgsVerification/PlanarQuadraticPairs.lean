import BfgsVerification.PlanarQuadraticCurve
import BfgsVerification.PairRealizability

/-! Actual differentiable crossing pairs and exact Armijo–weak-Wolfe eligibility. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.PlanarQuadraticExample
open TransportedCertificate RadialCertificate

def oldPoint (u ε : ℝ) : Vec 2 := ![u,tieHeight u+ε]
def newPoint (u ε : ℝ) : Vec 2 := ![u,tieHeight u-ε]
def oldGradient (u ε : ℝ) : Vec 2 := gradient 1 (oldPoint u ε)
def newGradient (u ε : ℝ) : Vec 2 := gradient 0 (newPoint u ε)

theorem winner_zero_value {x : Vec 2} (h1 : branch 1 x≤branch 0 x) (h2 : branch 2 x≤branch 0 x) :
    objective x=branch 0 x := max_eq_left (max_le h1 h2)

theorem winner_one_value {x : Vec 2} (h0 : branch 0 x≤branch 1 x) (h2 : branch 2 x≤branch 1 x) :
    objective x=branch 1 x := by rw [objective,max_eq_left h2,max_eq_right h0]

theorem winner_zero_hasGradient {x : Vec 2} (h1 : branch 1 x<branch 0 x) (h2 : branch 2 x<branch 0 x) :
    HasFDerivAt objective (gradientFunctional (gradient 0 x)) x := by
  have hc (i : Fin 3) := (branch_contDiff (N := 0) i).continuous.continuousAt (x := x)
  have he : objective =ᶠ[𝓝 x] branch 0 := by
    filter_upwards [(hc 1).eventually_lt (hc 0) h1,(hc 2).eventually_lt (hc 0) h2] with z hz1 hz2
    exact winner_zero_value hz1.le hz2.le
  exact (branch_hasGradient 0 x).congr_of_eventuallyEq he

theorem winner_one_hasGradient {x : Vec 2} (h0 : branch 0 x<branch 1 x) (h2 : branch 2 x<branch 1 x) :
    HasFDerivAt objective (gradientFunctional (gradient 1 x)) x := by
  have hc (i : Fin 3) := (branch_contDiff (N := 0) i).continuous.continuousAt (x := x)
  have he : objective =ᶠ[𝓝 x] branch 1 := by
    filter_upwards [(hc 0).eventually_lt (hc 1) h0,(hc 2).eventually_lt (hc 1) h2] with z hz0 hz2
    exact winner_one_value hz0.le hz2.le
  exact (branch_hasGradient 1 x).congr_of_eventuallyEq he

theorem oldPoint_continuous (u : ℝ) : Continuous (oldPoint u) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · change Continuous (fun ε : ℝ => tieHeight u+ε)
    fun_prop

theorem newPoint_continuous (u : ℝ) : Continuous (newPoint u) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · change Continuous (fun ε : ℝ => tieHeight u-ε)
    fun_prop

theorem pair_points_tendsto (u : ℝ) :
    Tendsto (oldPoint u) (𝓝[>] 0) (𝓝 (base u)) ∧
      Tendsto (newPoint u) (𝓝[>] 0) (𝓝 (base u)) := by
  exact ⟨by simpa [oldPoint,base] using ((oldPoint_continuous u).tendsto 0).mono_left nhdsWithin_le_nhds,
    by simpa [newPoint,base] using ((newPoint_continuous u).tendsto 0).mono_left nhdsWithin_le_nhds⟩

theorem crossing_branch_difference {u : ℝ} (hu : 0≤u) (ε : ℝ) :
    branch 0 (oldPoint u ε)-branch 1 (oldPoint u ε)= -ε*(1+2*tieHeight u+ε) ∧
    branch 0 (newPoint u ε)-branch 1 (newPoint u ε)= ε*(1+2*tieHeight u-ε) := by
  have he := tieHeight_equation hu
  simp only [branch,oldPoint,newPoint,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor <;> nlinarith

/-- Strict activity at both endpoints is derived from the actual tie curve and
positive third-branch gap, rather than supplied as input to the example. -/
theorem eventually_crossing_active {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      branch 0 (oldPoint u ε)<branch 1 (oldPoint u ε) ∧
      branch 2 (oldPoint u ε)<branch 1 (oldPoint u ε) ∧
      branch 1 (newPoint u ε)<branch 0 (newPoint u ε) ∧
      branch 2 (newPoint u ε)<branch 0 (newPoint u ε) := by
  have hold (i : Fin 3) : Tendsto (fun ε => branch i (oldPoint u ε)) (𝓝[>] 0) (𝓝 (branch i (base u))) :=
    ((branch_contDiff (N := 0) i).continuous.tendsto _).comp (pair_points_tendsto u).1
  have hnew (i : Fin 3) : Tendsto (fun ε => branch i (newPoint u ε)) (𝓝[>] 0) (𝓝 (branch i (base u))) :=
    ((branch_contDiff (N := 0) i).continuous.tendsto _).comp (pair_points_tendsto u).2
  have hgap := third_inactive_on_tie hu hsmall
  have hgap1 : branch 2 (base u)<branch 1 (base u) := by rwa [← tie_branch_values hu.le]
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0<ε := self_mem_nhdsWithin
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp,hs,(hold 2).eventually_lt (hold 1) hgap1,(hnew 2).eventually_lt (hnew 0) hgap]
    with ε hε hε1 h21 h20
  have he := crossing_branch_difference hu.le ε
  have hv := tieHeight_pos hu
  refine ⟨?_,h21,?_,h20⟩
  · have hp := mul_pos hε (show 0<1+2*tieHeight u+ε by linarith)
    linarith [he.1]
  · have hp := mul_pos hε (show 0<1+2*tieHeight u-ε by linarith)
    linarith [he.2]

theorem pair_step (u ε : ℝ) : pairStep (oldPoint u ε) (newPoint u ε)=![0,-2*ε] := by
  ext i
  fin_cases i <;> simp [pairStep,oldPoint,newPoint] <;> ring

theorem pair_decrease (u ε : ℝ) :
    pairDecrease (oldPoint u ε) (newPoint u ε) (oldGradient u ε)=2*ε*(1+3*tieHeight u+3*ε) := by
  rw [pairDecrease,pair_step]
  rw [oldGradient,(gradient_coordinates (oldPoint u ε)).2.1]
  simp [oldPoint,dot,Fin.sum_univ_two]
  ring

theorem pair_curvature (u ε : ℝ) :
    pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u ε) (newGradient u ε)=
      2*ε*(1+2*tieHeight u+4*ε) := by
  rw [pairCurvature,pair_step,oldGradient,newGradient,
    (gradient_coordinates (oldPoint u ε)).2.1,(gradient_coordinates (newPoint u ε)).1]
  simp [oldPoint,newPoint,dot,Fin.sum_univ_two]
  ring

theorem crossing_value_difference {u : ℝ} (hu : 0≤u) (ε : ℝ) :
    branch 1 (oldPoint u ε)-branch 0 (newPoint u ε)=ε*(1+4*tieHeight u)+ε^2 := by
  have he := tieHeight_equation hu
  simp only [branch,oldPoint,newPoint,Matrix.cons_val_zero,Matrix.cons_val_one]
  nlinarith

theorem radial_numerator {u : ℝ} (hu : 0≤u) (ε : ℝ) :
    radialNumerator 0 (newPoint u ε) (oldGradient u ε) (newGradient u ε)=
      u^2/2-(tieHeight u)^2+ε*(1-2*tieHeight u)+4*ε^2 := by
  have he := tieHeight_equation hu
  rw [radialNumerator,oldGradient,newGradient,
    (gradient_coordinates (oldPoint u ε)).2.1,(gradient_coordinates (newPoint u ε)).1]
  simp only [oldPoint,newPoint,sub_zero,dot,Fin.sum_univ_two,Pi.sub_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply]
  nlinarith

theorem eventually_eligible {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, EligiblePair objective (1/4) (1/2)
      (oldPoint u ε) (newPoint u ε) (oldGradient u ε) (newGradient u ε) := by
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0<ε := self_mem_nhdsWithin
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_crossing_active hu hsmall,hp,hs] with ε ha hε hε1
  have hv := tieHeight_pos hu
  have hvalues : objective (oldPoint u ε)-objective (newPoint u ε)=ε*(1+4*tieHeight u)+ε^2 := by
    rw [winner_one_value ha.1.le ha.2.1.le,winner_zero_value ha.2.2.1.le ha.2.2.2.le]
    exact crossing_value_difference hu.le ε
  have hd := pair_decrease u ε
  have ht := pair_curvature u ε
  refine ⟨winner_one_hasGradient ha.1 ha.2.1,winner_zero_hasGradient ha.2.2.1 ha.2.2.2,?_,?_,?_,?_⟩
  · rw [hd]
    positivity
  · rw [hd,hvalues]
    nlinarith [mul_pos hε (show 0<1+5*tieHeight u-ε by linarith)]
  · rw [hd,hvalues]
    nlinarith [mul_pos hε (show 0<1+2*tieHeight u+5*ε by linarith)]
  · rw [hd,ht]
    nlinarith [mul_pos hε (show 0<1+tieHeight u+5*ε by linarith)]

end BfgsVerification.PlanarQuadraticExample
