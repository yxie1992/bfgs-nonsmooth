import BfgsVerification.AlgebraicSeedDeterministicTrace
/-! D’s literal four-piece coercive deterministic full-BFGS counterexample.
This does not assert the later local C2 embedding theorem. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set
namespace BfgsVerification.SeedOrbit
open SeedCycle

def coerciveFamily : MaxAffine.Family 2 4 where
  a := ![g0,g1,g2 seedC seedD,![0,1]]
  b := ![0,0,0,-17]
  nonempty := ⟨0⟩
def coerciveObjective : Vec 2 → ℝ := coerciveFamily.objective

theorem coercive_branch_old (i : Fin 3) (x : Vec 2) :
    coerciveFamily.branch i.castSucc x=dot (gradient seedC seedD i) x := by
  fin_cases i <;> norm_num [coerciveFamily,MaxAffine.Family.branch,gradient,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

theorem coercive_branch_last (x : Vec 2) : coerciveFamily.branch 3 x=x 1-17 := by
  change dot (![0,1] : Vec 2) x+(-17)=x 1-17
  norm_num [dot,Fin.sum_univ_two]
  ring

theorem coercive_strict_active {x : Vec 2} {i : Fin 3} (h : PointCertificate seedC seedD x i) :
    ∀ j : Fin 4, j ≠ i.castSucc → coerciveFamily.branch j x < coerciveFamily.branch i.castSucc x := by
  intro j hj
  have he : j=3 ∨ ∃ k : Fin 3, j=k.castSucc := by
    by_cases h3 : j.val=3
    · left; exact Fin.ext h3
    · right
      have hjlt : j.val < 3 := by have := j.isLt; omega
      exact ⟨⟨j.val,hjlt⟩,rfl⟩
  rcases he with rfl | ⟨k,rfl⟩
  · rw [coercive_branch_last,coercive_branch_old]
    linarith [h.vertical,h.value_pos]
  · rw [coercive_branch_old,coercive_branch_old]
    apply h.active
    intro hki
    subst k
    exact hj rfl

theorem coercive_value_eq {x : Vec 2} {i : Fin 3} (h : PointCertificate seedC seedD x i) :
    coerciveObjective x=objective seedC seedD x := by
  rw [objective_of_active h.active]
  apply le_antisymm
  · unfold coerciveObjective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro j _
    by_cases hj : j=i.castSucc
    · subst j; exact (coercive_branch_old i x).le
    · simpa only [coercive_branch_old] using (coercive_strict_active h j hj).le
  · simpa only [coercive_branch_old] using coerciveFamily.branch_le i.castSucc x

theorem coercive_hasGradient {x : Vec 2} {i : Fin 3} (h : PointCertificate seedC seedD x i) :
    HasFDerivAt coerciveObjective (gradientFunctional (gradient seedC seedD i)) x := by
  have hh := coerciveFamily.strict_active_hasGradient (coercive_strict_active h)
  have he : coerciveFamily.a i.castSucc=gradient seedC seedD i := by
    fin_cases i <;> norm_num [coerciveFamily,gradient,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  rw [he] at hh
  exact hh

def coerciveOptimizer : Vec 2 := ![-1,16]

theorem coercive_minimum_value : coerciveObjective coerciveOptimizer = -1 := by
  have hold := source_downhill_pairings
  have hb (i : Fin 3) : coerciveFamily.branch i.castSucc coerciveOptimizer ≤ -1 := by
    rw [coercive_branch_old]
    change dot (gradient seedC seedD i) downhill ≤ -1
    fin_cases i
    · exact hold.1.le
    · exact hold.2.1.le
    · exact hold.2.2.le
  apply le_antisymm
  · unfold coerciveObjective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro j _
    fin_cases j
    · exact hb 0
    · exact hb 1
    · exact hb 2
    · change coerciveFamily.branch 3 coerciveOptimizer ≤ -1
      rw [coercive_branch_last]
      norm_num [coerciveOptimizer]
  · have hh := coerciveFamily.branch_le 0 coerciveOptimizer
    change coerciveFamily.branch (0:Fin 3).castSucc coerciveOptimizer ≤ _ at hh
    rw [coercive_branch_old] at hh
    change dot (gradient seedC seedD 0) downhill ≤ _ at hh
    rwa [source_downhill_pairings.1] at hh

theorem coercive_coordinate_bounds (x : Vec 2) :
    x 0 ≤ coerciveObjective x ∧ -x 0-x 1/8 ≤ coerciveObjective x ∧ x 1-17 ≤ coerciveObjective x := by
  have h0 := coerciveFamily.branch_le (0:Fin 3).castSucc x
  have h1 := coerciveFamily.branch_le (1:Fin 3).castSucc x
  have h3 := coerciveFamily.branch_le 3 x
  rw [coercive_branch_old] at h0 h1
  rw [coercive_branch_last] at h3
  norm_num [gradient,g0,g1,dot,Fin.sum_univ_two] at h0 h1
  change -x 0 ≤ coerciveObjective x+(1/8)*x 1 at h1
  exact ⟨h0,by linarith,h3⟩

theorem coercive_lower_bound (x : Vec 2) : -1 ≤ coerciveObjective x := by
  obtain ⟨h0,h1,h3⟩ := coercive_coordinate_bounds x
  linarith

theorem coercive_unique_optimizer {x : Vec 2} (hx : coerciveObjective x = -1) : x=coerciveOptimizer := by
  obtain ⟨h0,h1,h3⟩ := coercive_coordinate_bounds x
  rw [hx] at h0 h1 h3
  ext i
  fin_cases i <;> norm_num [coerciveOptimizer] <;> linarith

theorem coercive_sublevels_compact (a : ℝ) : IsCompact {x | coerciveObjective x ≤ a} := by
  apply Localization.sublevel_compact coerciveFamily.objective_convex coerciveOptimizer
  · intro x
    change coerciveObjective coerciveOptimizer ≤ coerciveObjective x
    rw [coercive_minimum_value]
    exact coercive_lower_bound x
  · intro x hx
    change coerciveObjective x=coerciveObjective coerciveOptimizer at hx
    rw [coercive_minimum_value] at hx
    exact coercive_unique_optimizer hx

theorem coercive_orbit_certificate (k : ℕ) :
    PointCertificate seedC seedD (orbitPoint k) (phase k) :=
  (source_base_certificate (phase k)).scale (orbitScale_pos k) (orbitScale_le_one k)

theorem coercive_orbit_value (k : ℕ) : coerciveObjective (orbitPoint k)=objective seedC seedD (orbitPoint k) :=
  coercive_value_eq (coercive_orbit_certificate k)

theorem coercive_orbit_hasGradient (k : ℕ) :
    HasFDerivAt coerciveObjective (gradientFunctional (orbitGradient k)) (orbitPoint k) :=
  coercive_hasGradient (coercive_orbit_certificate k)

def coerciveRun (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    AdmissibleBFGSRun 2 coerciveObjective where
  convex := coerciveFamily.objective_convex
  x := orbitPoint
  H := orbitMetric
  g := orbitGradient
  α := orbitLength
  c₁ := c₁
  c₂ := c₂
  c₁_pos := hc₁
  c₁_lt_c₂ := hc
  c₂_lt_one := hc₂
  initial_posDef := (run c₁ c₂ hc₁ hc₁' hc hc₂).initial_posDef
  alpha_pos k := source_length_pos (phase k)
  gradient_nonzero k := source_gradient_nonzero (phase k)
  hasGradient := coercive_orbit_hasGradient
  step := orbit_step
  update := orbit_update
  armijo k := by
    rw [coercive_orbit_value,coercive_orbit_value]
    exact (orbit_strict_accept hc₁ hc₁' (hc₁.trans hc) k).1.le
  weak_wolfe k := (orbit_strict_accept hc₁ hc₁' (hc₁.trans hc) k).2.le


open DeterministicLineSearch

theorem coercive_scaled_predicates {t c₁ c₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (q : Fin 9) :
    (Armijo coerciveObjective (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₁ (trialLength q) ↔
    Armijo (objective seedC seedD) (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₁ (trialLength q)) ∧
    (Wolfe coerciveObjective (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₂ (trialLength q) ↔
    Wolfe (objective seedC seedD) (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₂ (trialLength q)) := by
  have hb := (source_base_certificate (trialPhase q)).scale ht ht1
  have hq := (source_trial_certificate q).toPointCertificate.scale ht ht1
  have hx := coercive_value_eq hb
  have hy := coercive_value_eq hq
  have hg := coercive_hasGradient hq
  have hg' := hasGradient_of_active hq.active
  constructor
  · unfold Armijo
    rw [scaled_trial,hx]
    change coerciveObjective (t • trial seedC seedD seedRatio (trialPhase q) (trialLength q)) < _ ↔ _
    rw [hy]
    rfl
  · unfold Wolfe
    rw [scaled_trial]
    change _ < dot (coordinateGradient coerciveObjective (t • trial seedC seedD seedRatio (trialPhase q) (trialLength q))) _ ↔
      _ < dot (coordinateGradient (objective seedC seedD) (t • trial seedC seedD seedRatio (trialPhase q) (trialLength q))) _
    rw [actual_coordinateGradient hg,actual_coordinateGradient hg']

theorem coercive_scaled_accept {t c₁ c₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (q : Fin 9) (hq : trialAccept q=true) :
    Armijo coerciveObjective (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₁ (trialLength q) ∧
    Wolfe coerciveObjective (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₂ (trialLength q) := by
  have h := source_scaled_accept ht hc₁ hc₁' hc₂ q hq
  have he := coercive_scaled_predicates (c₁ := c₁) (c₂ := c₂) ht ht1 q
  exact ⟨he.1.mpr h.1,he.2.mpr h.2⟩

theorem coercive_scaled_reject {t c₁ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc₁ : 0 < c₁)
    (q : Fin 9) (hq : trialAccept q=false) :
    ¬ Armijo coerciveObjective (t • point seedC seedD seedRatio (trialPhase q))
      (t • direction seedC seedD seedRatio (trialPhase q)) (gradient seedC seedD (trialPhase q)) c₁ (trialLength q) := by
  have h := source_scaled_reject ht hc₁ q hq
  have he := (coercive_scaled_predicates (c₁ := c₁) (c₂ := 1/2) ht ht1 q).1
  exact fun ha => h (he.mp ha)
theorem coercive_scaled_search_zero {t c₁ c₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    search coerciveObjective (t • point seedC seedD seedRatio 0)
      (t • direction seedC seedD seedRatio 0) (gradient seedC seedD 0) c₁ c₂ 5 0 none 1 =
        (some 1,[1]) := by
  obtain ⟨ha,hw⟩ := coercive_scaled_accept ht ht1 hc₁ hc₁' hc₂ 0 rfl
  exact search_accept 4 ha hw

theorem coercive_scaled_search_one {t c₁ c₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    search coerciveObjective (t • point seedC seedD seedRatio 1)
      (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ c₂ 5 0 none 1 =
        (some (1/4),[1,1/2,1/4]) := by
  have h1 := coercive_scaled_reject ht ht1 hc₁ 1 rfl
  have h2 := coercive_scaled_reject ht ht1 hc₁ 2 rfl
  obtain ⟨ha,hw⟩ := coercive_scaled_accept ht ht1 hc₁ hc₁' hc₂ 3 rfl
  change ¬ Armijo coerciveObjective (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ (1) at h1
  change ¬ Armijo coerciveObjective (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ (1/2) at h2
  change Armijo coerciveObjective (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₁ (1/4) at ha
  change Wolfe coerciveObjective (t • point seedC seedD seedRatio 1) (t • direction seedC seedD seedRatio 1) (gradient seedC seedD 1) c₂ (1/4) at hw
  rw [search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_accept 2 ha hw]
  exact ⟨rfl,rfl⟩

theorem coercive_scaled_search_two {t c₁ c₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) :
    search coerciveObjective (t • point seedC seedD seedRatio 2)
      (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ c₂ 5 0 none 1 =
        (some (1/16),[1,1/2,1/4,1/8,1/16]) := by
  have h1 := coercive_scaled_reject ht ht1 hc₁ 4 rfl
  have h2 := coercive_scaled_reject ht ht1 hc₁ 5 rfl
  have h3 := coercive_scaled_reject ht ht1 hc₁ 6 rfl
  have h4 := coercive_scaled_reject ht ht1 hc₁ 7 rfl
  obtain ⟨ha,hw⟩ := coercive_scaled_accept ht ht1 hc₁ hc₁' hc₂ 8 rfl
  change ¬ Armijo coerciveObjective (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1) at h1
  change ¬ Armijo coerciveObjective (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/2) at h2
  change ¬ Armijo coerciveObjective (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/4) at h3
  change ¬ Armijo coerciveObjective (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/8) at h4
  change Armijo coerciveObjective (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₁ (1/16) at ha
  change Wolfe coerciveObjective (t • point seedC seedD seedRatio 2) (t • direction seedC seedD seedRatio 2) (gradient seedC seedD 2) c₂ (1/16) at hw
  rw [search_armijo_reject 4 h1]
  norm_num only [zero_add]
  rw [search_armijo_reject 3 h2]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_armijo_reject 2 h3]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_armijo_reject 1 h4]
  norm_num only [zero_add,div_div]
  norm_num
  rw [search_accept 0 ha hw]
  exact ⟨rfl,rfl⟩

theorem coercive_scaled_search {t c₁ c₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (j : Fin 3) :
    search coerciveObjective (t • point seedC seedD seedRatio j)
      (t • direction seedC seedD seedRatio j) (gradient seedC seedD j) c₁ c₂ 5 0 none 1 =
        (some (length j),trialHistory j) := by
  fin_cases j
  · exact coercive_scaled_search_zero ht ht1 hc₁ hc₁' hc₂
  · exact coercive_scaled_search_one ht ht1 hc₁ hc₁' hc₂
  · exact coercive_scaled_search_two ht ht1 hc₁ hc₁' hc₂


theorem coercive_orbit_search {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂) (k : ℕ) :
    fromMetric coerciveObjective (orbitPoint k) (orbitMetric k) c₁ c₂ 5 =
      (some (orbitLength k),trialHistory (phase k)) := by
  unfold fromMetric
  rw [actual_coordinateGradient (coercive_orbit_hasGradient k)]
  simp only [orbitPoint,orbitMetric,orbitGradient,orbitLength,bfgsStep_scale_matrix,source_direction,one_smul]
  exact coercive_scaled_search (orbitScale_pos k) (orbitScale_le_one k) hc₁ hc₁' hc₂ (phase k)

theorem coercive_orbit_values_tendsto : Tendsto (fun k => coerciveObjective (orbitPoint k)) atTop (𝓝 0) := by
  simpa only [coercive_orbit_value] using orbit_value_tendsto

theorem coercive_zero_value : coerciveObjective 0=0 := by
  have h := (convex_continuous coerciveFamily.objective_convex).continuousAt.tendsto.comp orbitPoint_tendsto
  change Tendsto (fun k => coerciveObjective (orbitPoint k)) atTop (𝓝 (coerciveObjective 0)) at h
  exact tendsto_nhds_unique h coercive_orbit_values_tendsto

theorem coercive_limit_not_stationary :
    (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential coerciveObjective 0 := by
  intro h
  have hh := h coerciveOptimizer
  rw [coercive_minimum_value,coercive_zero_value] at hh
  norm_num [dot] at hh

theorem coercive_all_trials_hasGradient (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    HasFDerivAt coerciveObjective (gradientFunctional (gradient seedC seedD (trialActive q)))
      (orbitPoint k+trialLength q • bfgsStep (orbitMetric k) (orbitGradient k) 1) :=
  coercive_hasGradient (orbit_trial_point_certificate k q hq)

theorem actual_coercive_deterministic_failure {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3)
    (hc : c₁ < c₂) (hc₂ : c₂ < 1) :
    let R := coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂
    (∀ a : ℝ, IsCompact {x | coerciveObjective x ≤ a}) ∧
      coerciveObjective coerciveOptimizer = -1 ∧
      (∀ x, -1 ≤ coerciveObjective x) ∧
      (∀ x, coerciveObjective x = -1 → x=coerciveOptimizer) ∧
      R.H 0=1 ∧ Tendsto R.x atTop (𝓝 0) ∧
      Tendsto (fun k => coerciveObjective (R.x k)) atTop (𝓝 0) ∧
      (∀ k, 0 < coerciveObjective (R.x k)) ∧
      (∀ k, coerciveObjective (R.x (k+1)) < coerciveObjective (R.x k)) ∧
      (0 : Vec 2) ∉ ConvexSubdifferential.subdifferential coerciveObjective 0 ∧
      (∀ k, fromMetric coerciveObjective (R.x k) (R.H k) c₁ c₂ 5 =
        (some (R.α k),trialHistory (phase k))) := by
  refine ⟨coercive_sublevels_compact,coercive_minimum_value,coercive_lower_bound,
    fun _ h => coercive_unique_optimizer h,?_,orbitPoint_tendsto,coercive_orbit_values_tendsto,?_,?_,
    coercive_limit_not_stationary,coercive_orbit_search hc₁ hc₁' (hc₁.trans hc)⟩
  · change (1:ℝ) • (1:Mat 2)=1
    rw [one_smul]
  · intro k
    change 0 < coerciveObjective (orbitPoint k)
    rw [coercive_orbit_value]
    exact orbit_value_pos k
  · exact (coerciveRun c₁ c₂ hc₁ hc₁' hc hc₂).objective_strict_decrease


end BfgsVerification.SeedOrbit
