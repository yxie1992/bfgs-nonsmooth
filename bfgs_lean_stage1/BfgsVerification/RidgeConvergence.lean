import BfgsVerification.RidgeCorrectness
import BfgsVerification.RidgeContours

noncomputable section
open scoped Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification.RidgeSupersession

theorem fullBFGS_convergence {a b : ℝ → ℝ}
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b)
    {p q u : ℝ} (hp : 0<p) (hq : 0<q)
    (hmin : ∀t,profile a b p q u ≤ profile a b p q t)
    (hunique : ∀t,profile a b p q t=profile a b p q u → t=u)
    (ha'' : ∀t,t≠u → 0<deriv (deriv a) t)
    (hb'' : ∀t,t≠u → 0<deriv (deriv b) t)
    (R : AdmissibleBFGSRun 2 (objective a b p q)) :
    Tendsto (fun k => objective a b p q (R.x k)) atTop (𝓝 (profile a b p q u)) ∧
      Tendsto R.x atTop (𝓝 (optimizer a b p q u)) := by
  have hm := optimizer_minimum hp hq hmin
  have hu := optimizer_unique hp hq hmin hunique
  have hK := R.initialSublevel_compact_of_unique_minimizer (optimizer a b p q u) hm hu
  obtain ⟨hv,_,_,hx⟩ := R.planar_convergence_on_sublevel (optimizer a b p q u) hm
    (objective a b p q (R.x 0)) hK le_rfl
    (fun level _ _ => strict_contours (strictConvex_of_second_pos_except ha u ha'')
      (strictConvex_of_second_pos_except hb u hb'') hp hq level)
    (fun x _ hn => source_regular ha hb hca hcb hp hq x hn)
    (fun x _ => source_affineCorrect ha hb hca hcb hp hq hmin hunique x)
  exact ⟨by simpa only [objective_optimizer (add_pos hp hq).ne'] using hv,hx hu⟩

/-- The source localization follows with an objective-gap neighborhood chosen
before every actual run, initial SPD metric and admissible line search. -/
theorem localized_fullBFGS_convergence {a b : ℝ → ℝ}
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b)
    {p q u : ℝ} (hp : 0<p) (hq : 0<q)
    (hmin : ∀t,profile a b p q u ≤ profile a b p q t)
    (hunique : ∀t,profile a b p q t=profile a b p q u → t=u)
    (ha'' : ∀t,t≠u → 0<deriv (deriv a) t)
    (hb'' : ∀t,t≠u → 0<deriv (deriv b) t)
    (U : Set (Vec 2)) (hU : U∈𝓝 (optimizer a b p q u)) :
    ∃ε : ℝ,0<ε ∧ ∀R : AdmissibleBFGSRun 2 (objective a b p q),
      objective a b p q (R.x 0) ≤ profile a b p q u+ε →
      (∀k,R.x k∈U) ∧
      Tendsto (fun k => objective a b p q (R.x k)) atTop (𝓝 (profile a b p q u)) ∧
      Tendsto R.x atTop (𝓝 (optimizer a b p q u)) := by
  obtain ⟨ε,hε,hsub⟩ := Localization.neighborhood_basin (objective_convex hca hcb p q)
    (optimizer a b p q u) (optimizer_minimum hp hq hmin) (optimizer_unique hp hq hmin hunique) hU
  refine ⟨ε,hε,?_⟩
  intro R hstart
  refine ⟨?_,fullBFGS_convergence ha hb hca hcb hp hq hmin hunique ha'' hb'' R⟩
  intro k
  apply hsub
  rw [objective_optimizer (add_pos hp hq).ne']
  exact (R.objective_le_initial k).trans hstart

def RidgeSupersessionTarget : Prop := ∀a b : ℝ → ℝ,
    ContDiff ℝ 2 a → ContDiff ℝ 2 b → ConvexOn ℝ univ a → ConvexOn ℝ univ b →
    ∀p q u : ℝ,0<p → 0<q →
    (∀t,profile a b p q u ≤ profile a b p q t) →
    (∀t,profile a b p q t=profile a b p q u → t=u) →
    (∀t,t≠u → 0<deriv (deriv a) t) →
    (∀t,t≠u → 0<deriv (deriv b) t) →
    (∀R : AdmissibleBFGSRun 2 (objective a b p q),
      Tendsto (fun k => objective a b p q (R.x k)) atTop (𝓝 (profile a b p q u)) ∧
      Tendsto R.x atTop (𝓝 (optimizer a b p q u))) ∧
    (∀U : Set (Vec 2),U∈𝓝 (optimizer a b p q u) →
      ∃ε : ℝ,0<ε ∧ ∀R : AdmissibleBFGSRun 2 (objective a b p q),
        objective a b p q (R.x 0) ≤ profile a b p q u+ε →
        (∀k,R.x k∈U) ∧
        Tendsto (fun k => objective a b p q (R.x k)) atTop (𝓝 (profile a b p q u)) ∧
        Tendsto R.x atTop (𝓝 (optimizer a b p q u)))

theorem ridgeSupersession : RidgeSupersessionTarget := by
  intro a b ha hb hca hcb p q u hp hq hmin hunique ha'' hb''
  exact ⟨fullBFGS_convergence ha hb hca hcb hp hq hmin hunique ha'' hb'',
    localized_fullBFGS_convergence ha hb hca hcb hp hq hmin hunique ha'' hb''⟩

end BfgsVerification.RidgeSupersession
