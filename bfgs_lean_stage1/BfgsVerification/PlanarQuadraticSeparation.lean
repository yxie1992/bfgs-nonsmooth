import BfgsVerification.PlanarQuadraticPairs
import BfgsVerification.PlanarQuadraticConvergence

/-! C's fixed-positive-band RS failure through actual eligible full-BFGS steps. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.PlanarQuadraticExample
open TransportedCertificate RadialCertificate

theorem radial_numerator_tendsto {u : ℝ} (hu : 0≤u) :
    Tendsto (fun ε => radialNumerator 0 (newPoint u ε) (oldGradient u ε) (newGradient u ε))
      (𝓝[>] 0) (𝓝 (u^2/2-(tieHeight u)^2)) := by
  simp_rw [radial_numerator hu]
  have hc : Continuous (fun ε : ℝ => u^2/2-(tieHeight u)^2+ε*(1-2*tieHeight u)+4*ε^2) := by fun_prop
  simpa only [zero_mul,zero_pow (by decide : 2≠0),mul_zero,add_zero] using
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem pair_decrease_tendsto (u : ℝ) :
    Tendsto (fun ε => pairDecrease (oldPoint u ε) (newPoint u ε) (oldGradient u ε))
      (𝓝[>] 0) (𝓝 0) := by
  simp_rw [pair_decrease]
  have hc : Continuous (fun ε : ℝ => 2*ε*(1+3*tieHeight u+3*ε)) := by fun_prop
  simpa only [mul_zero,zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem pair_curvature_tendsto {u : ℝ} (hu : 0<u) :
    Tendsto (fun ε => pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u ε) (newGradient u ε))
      (𝓝[>] 0) (𝓝[>] 0) := by
  simp_rw [pair_curvature]
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · have hc : Continuous (fun ε : ℝ => 2*ε*(1+2*tieHeight u+4*ε)) := by fun_prop
    simpa only [mul_zero,zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0<ε := self_mem_nhdsWithin
    filter_upwards [hp] with ε hε
    have hv := tieHeight_pos hu
    change 0<2*ε*(1+2*tieHeight u+4*ε)
    positivity

theorem radial_quotient_tendsto {u : ℝ} (hu : 0<u) (hsmall : u<1/10) :
    Tendsto (fun ε => (radialNumerator 0 (newPoint u ε) (oldGradient u ε) (newGradient u ε))^2 /
      pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u ε) (newGradient u ε))
      (𝓝[>] 0) atTop := by
  have hn := (radial_numerator_tendsto hu.le).pow 2
  have hpos := sq_pos_of_ne_zero (tie_radial_jump_neg hu hsmall).ne
  simpa only [div_eq_mul_inv] using
    hn.pos_mul_atTop hpos (pair_curvature_tendsto hu).inv_tendsto_nhdsGT_zero

/-- The positive band is selected before every predicted-decrease threshold
and candidate RS bound. Eligibility, actual endpoint gradients and an actual
SPD full-BFGS direction realization are all conclusions. -/
theorem eligible_radial_unbounded_on_neighborhood {K : Set (Vec 2)} (hK : K∈𝓝 (0 : Vec 2)) :
    ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → ∀ C : ℝ,
      ∃ x z g h : Vec 2, ∃ H : Mat 2,
        x∈K ∧ z∈K ∧ η≤objective z ∧ objective z≤objective x ∧
        EligiblePair objective (1/4) (1/2) x z g h ∧ pairDecrease x z g≤δ ∧
        H.PosDef ∧ bfgsStep H g 1=pairStep x z ∧
        C*pairCurvature x z g h<(radialNumerator 0 z g h)^2 := by
  obtain ⟨u,hu,hsmall,hKu⟩ := exists_positive_tie_base hK
  have hb : 0<objective (base u) := by
    have hl := objective_lower (base u)
    simp only [sqNorm,base,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hl
    change 0<objective ![u,tieHeight u]
    nlinarith [sq_pos_of_pos hu,sq_nonneg (tieHeight u)]
  refine ⟨objective (base u)/2,by positivity,?_⟩
  intro δ hδ C
  have hband : ∀ᶠ ε : ℝ in 𝓝[>] 0, objective (base u)/2<objective (newPoint u ε) :=
    (((convex_continuous objective_convex).tendsto (base u)).comp (pair_points_tendsto u).2).eventually
      (eventually_gt_nhds (by linarith))
  have hd := (pair_decrease_tendsto u).eventually (eventually_lt_nhds hδ)
  have hr := (radial_quotient_tendsto hu hsmall).eventually (eventually_gt_atTop C)
  obtain ⟨ε,hpair,hx,hz,hbandε,hdε,hrε⟩ :=
    ((eventually_eligible hu hsmall).and (((pair_points_tendsto u).1.eventually hKu).and
      (((pair_points_tendsto u).2.eventually hKu).and (hband.and (hd.and hr))))).exists
  have ht : 0<pairCurvature (oldPoint u ε) (newPoint u ε) (oldGradient u ε) (newGradient u ε) := by
    have hc := hpair.curvature
    have hd := hpair.decrease_pos
    nlinarith
  obtain ⟨H,hH,hstep,henergy⟩ := eligible_pair_realizable hpair
  refine ⟨oldPoint u ε,newPoint u ε,oldGradient u ε,newGradient u ε,H,
    hx,hz,hbandε.le,?_,hpair,hdε.le,hH,hstep,?_⟩
  · have ha := hpair.armijo
    have hd := hpair.decrease_pos
    linarith
  · exact (lt_div_iff₀ ht).mp hrε

theorem not_radial_secant_on_neighborhood {K : Set (Vec 2)} (hK : K∈𝓝 (0 : Vec 2)) :
    ¬HasRadialSecantBounds objective K 0 := by
  obtain ⟨η,hη,hex⟩ := eligible_radial_unbounded_on_neighborhood hK
  intro hRS
  obtain ⟨C,hC⟩ := hRS η hη
  obtain ⟨x,z,g,h,H,hx,hz,hband,horder,hpair,hd,hH,hstep,hexcess⟩ := hex 1 zero_lt_one C
  have ht : 0<secantCurvature x z g h := by
    change 0<pairCurvature x z g h
    have hc := hpair.curvature
    have hd := hpair.decrease_pos
    nlinarith
  have hbound := hC x z g h hx hz (by simpa only [objective_zero,zero_add] using hband)
    horder hpair.gradient_x hpair.gradient_z ht
  exact (not_lt_of_ge hbound) hexcess

theorem not_radial_secant_on_sublevel {b : ℝ} (hb : 0<b) :
    ¬HasRadialSecantBounds objective {x | objective x≤b} 0 := by
  apply not_radial_secant_on_neighborhood
  have hn : {x | objective x<b}∈𝓝 (0 : Vec 2) :=
    (isOpen_lt (convex_continuous objective_convex) continuous_const).mem_nhds (by change objective 0<b; rwa [objective_zero])
  exact mem_of_superset hn (fun x (hx : objective x<b) => show objective x≤b from hx.le)

theorem converges_without_radial_secant (R : AdmissibleBFGSRun 2 objective)
    (hstart : objective (R.x 0)<1/100) :
    Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) ∧
      ∀ K : Set (Vec 2), K∈𝓝 (0 : Vec 2) → ¬HasRadialSecantBounds objective K 0 := by
  exact ⟨(fullBFGS_explicit_basin R hstart).1,(fullBFGS_explicit_basin R hstart).2,
    fun K hK => not_radial_secant_on_neighborhood hK⟩

/-- The printed O(u³) statement on the positive source domain follows from the
proved literal cubic bound. -/
theorem tieHeight_expansion :
    (fun u : ℝ => tieHeight u-u+u^2/2) =O[𝓝[>] 0] (fun u : ℝ => u^3) := by
  apply Asymptotics.IsBigO.of_bound 1
  have hp : ∀ᶠ u : ℝ in 𝓝[>] 0, 0<u := self_mem_nhdsWithin
  have hs : ∀ᶠ u : ℝ in 𝓝[>] 0, u<1/10 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/10)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp,hs] with u hu hsmall
  simpa only [one_mul,Real.norm_eq_abs,abs_of_pos (pow_pos hu 3)] using tieHeight_cubic_remainder hu hsmall

end BfgsVerification.PlanarQuadraticExample
