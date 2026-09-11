import BfgsVerification.ScalarCounterexamples
import BfgsVerification.ConvexDifferentiability

/-! Differentiable Armijo--weak-Wolfe steps with finitely many forbidden ray times. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.FiniteRayLineSearch

theorem negative_derivative_descends {ψ : ℝ → ℝ} {a : ℝ}
    (hd : HasDerivAt ψ a 0) (ha : a < 0) : ∃ u : ℝ, 0 < u ∧ ψ u < ψ 0 := by
  have he := hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds ha)
  obtain ⟨u,hu,hup⟩ := (he.and self_mem_nhdsWithin).exists
  have hp : 0 < u := hup
  simp only [zero_add,smul_eq_mul] at hu
  refine ⟨u,hp,?_⟩
  by_contra hn
  have hh : 0 ≤ ψ u-ψ 0 := sub_nonneg.mpr (le_of_not_gt hn)
  exact not_lt_of_ge (mul_nonneg (inv_pos.mpr hp).le hh) hu

/-- A whole nonempty open interval satisfies strict Armijo, and every actual
scalar derivative on it satisfies strict weak Wolfe. No finite-switching
hypothesis or convergence premise is used to construct the interval. -/
theorem acceptable_interval {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    {a c₁ c₂ : ℝ} (hd : HasDerivAt φ a 0) (ha : a < 0)
    (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ φ t) :
    ∃ l u : ℝ, 0 < l ∧ l < u ∧ ∀ t ∈ Ioo l u,
      φ t < φ 0+c₁*a*t ∧ ∀ b : ℝ, HasDerivAt φ b t → c₂*a < b := by
  let d := (c₁+c₂)/2
  have hd1 : c₁ < d := by dsimp [d]; linarith
  have hd2 : d < c₂ := by dsimp [d]; linarith
  have hdp : 0 < d := hc₁.trans hd1
  have hdn : d < 1 := hd2.trans hc₂
  let ψ := fun t : ℝ => φ t-d*a*t
  have hψd : HasDerivAt ψ (a-d*a) 0 := by
    simpa only [mul_one] using hd.sub ((hasDerivAt_id 0).const_mul (d*a))
  have han : a-d*a < 0 := by nlinarith [mul_neg_of_neg_of_pos ha (show 0 < 1-d by linarith)]
  obtain ⟨v,hv,hdesc⟩ := negative_derivative_descends hψd han
  have hq : 0 < -d*a := mul_pos_of_neg_of_neg (neg_neg_of_pos hdp) ha
  obtain ⟨M,hM⟩ := exists_gt (max v ((φ 0-L)/(-d*a)))
  have hvM : v < M := (le_max_left _ _).trans_lt hM
  have hM0 : 0 < M := hv.trans hvM
  have hMt : (φ 0-L)/(-d*a) < M := (le_max_right _ _).trans_lt hM
  have hmul := (div_lt_iff₀ hq).mp hMt
  have hψM : ψ 0 < ψ M := by
    have hh := hL M hM0.le
    dsimp only [ψ]
    nlinarith
  have hcontφ : Continuous φ := continuous_iff_continuousOn_univ.mpr (hφ.continuousOn isOpen_univ)
  have hcont : Continuous ψ := hcontφ.sub (continuous_const.mul continuous_id)
  obtain ⟨z,hz,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hM0.le) hcont.continuousOn
  have hzv : ψ z ≤ ψ v := hmin ⟨hv.le,hvM.le⟩
  have hz0 : ψ z < ψ 0 := hzv.trans_lt hdesc
  have hzp : 0 < z := by
    apply lt_of_le_of_ne hz.1
    intro he
    rw [← he] at hz0
    exact lt_irrefl _ hz0
  have hzM : z < M := by
    apply lt_of_le_of_ne hz.2
    intro he
    rw [he] at hz0
    exact (not_lt_of_ge hψM.le) hz0
  have haz : φ z < φ 0+c₁*a*z := by
    have hda : d*a < c₁*a := mul_lt_mul_of_neg_right hd1 ha
    have hdz := mul_lt_mul_of_pos_right hda hzp
    dsimp only [ψ] at hz0
    nlinarith
  have hopen : IsOpen {t : ℝ | φ t < φ 0+c₁*a*t} :=
    isOpen_lt hcontφ (continuous_const.add (continuous_const.mul continuous_id))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds haz)
  let u := min M (z+ε)
  have hzu : z < u := lt_min hzM (by linarith)
  refine ⟨z,u,hzp,hzu,?_⟩
  intro t ht
  have htM : t < M := ht.2.trans_le (min_le_left _ _)
  have htε : t < z+ε := ht.2.trans_le (min_le_right _ _)
  have ht0 : 0 < t := hzp.trans ht.1
  have hs : φ t < φ 0+c₁*a*t := hball (by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr ht.1)]
    linarith)
  refine ⟨hs,?_⟩
  intro b hb
  have hmt : ψ z ≤ ψ t := hmin ⟨ht0.le,htM.le⟩
  have hsec : d*a ≤ slope φ z t := by
    rw [slope_def_field]
    apply (le_div_iff₀ (sub_pos.mpr ht.1)).mpr
    dsimp only [ψ] at hmt
    nlinarith
  have hder := hφ.slope_le_of_hasDerivAt (mem_univ z) (mem_univ t) ht.1 hb
  exact (mul_lt_mul_of_neg_right hd2 ha).trans_le (hsec.trans hder)

theorem ray_convex {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (x p : Vec n) : ConvexOn ℝ univ (fun t : ℝ => F (x+t • p)) := by
  refine ⟨convex_univ,?_⟩
  intro t _ u _ a b ha hb hab
  have he : x+(a*t+b*u) • p = a • (x+t • p)+b • (x+u • p) := by
    have hx : a • x+b • x=x := by rw [← add_smul,hab,one_smul]
    calc
      _ = (a • x+b • x)+(a*t+b*u) • p := by rw [hx]
      _ = _ := by module
  simpa only [smul_eq_mul,he] using hF.2 (mem_univ (x+t • p)) (mem_univ (x+u • p)) ha hb hab

theorem ray_hasDerivAt {n : ℕ} {F : Vec n → ℝ} (x p : Vec n) (t : ℝ) {g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) (x+t • p)) :
    HasDerivAt (fun u : ℝ => F (x+u • p)) (dot g p) t := by
  have hr : HasDerivAt (fun u : ℝ => x+u • p) p t := by
    simpa only [one_smul] using ((hasDerivAt_id t).smul_const p).const_add x
  simpa only [gradientFunctional_apply] using hg.comp_hasDerivAt t hr

/-- Finite full-space nondifferentiability along a bounded-below descent ray
suffices for an actual differentiable strict Armijo--weak-Wolfe trial. -/
theorem finite_nondifferentiability_step {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (x p g : Vec n)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hdes : dot g p < 0)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+t • p))
    (hbad : {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ F (x+t • p)}.Finite) :
    ∃ t : ℝ, ∃ h : Vec n, 0 < t ∧
      HasFDerivAt F (gradientFunctional h) (x+t • p) ∧
      F (x+t • p) < F x+c₁*dot g (t • p) ∧
      c₂*dot g (t • p) < dot h (t • p) := by
  have hd : HasDerivAt (fun t : ℝ => F (x+t • p)) (dot g p) 0 :=
    ray_hasDerivAt x p 0 (by simpa only [zero_smul,add_zero] using hg)
  obtain ⟨l,u,hl,hlu,hacc⟩ := acceptable_interval (ray_convex hF x p) hd hdes hc₁ hc hc₂ L hL
  obtain ⟨t,ht,hnot⟩ := (Ioo_infinite hlu).exists_not_mem_finite hbad
  have ht0 : 0 < t := hl.trans ht.1
  have hdiff : DifferentiableAt ℝ F (x+t • p) := by
    by_contra hn
    exact hnot ⟨ht0,hn⟩
  let h := coordinateGradient F (x+t • p)
  have hh : HasFDerivAt F (gradientFunctional h) (x+t • p) := hasFDerivAt_coordinateGradient hdiff
  have htrial := hacc t ht
  refine ⟨t,h,ht0,hh,?_,?_⟩
  · simpa only [zero_smul,add_zero,dot_smul_right,mul_assoc,mul_comm,mul_left_comm] using htrial.1
  · have hsl := htrial.2 (dot h p) (ray_hasDerivAt x p t hh)
    have hm := mul_lt_mul_of_pos_left hsl ht0
    simpa only [dot_smul_right,mul_assoc,mul_comm,mul_left_comm] using hm

theorem bfgsStep_scaling {n : ℕ} (H : Mat n) (g : Vec n) (α : ℝ) :
    bfgsStep H g α = α • bfgsStep H g 1 := by
  simp only [bfgsStep,smul_smul]
  congr 1
  ring

/-- Exact actual-full-BFGS form of the source finite-ray-singularity existence
claim, with initial SPD and an actual nonzero initial gradient. -/
theorem fullBFGS_step_exists {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hgn : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+bfgsStep H g t))
    (hbad : {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ F (x+bfgsStep H g t)}.Finite) :
    ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt F (gradientFunctional h) (x+bfgsStep H g α) ∧
      F (x+bfgsStep H g α) < F x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  have he : dot g (bfgsStep H g 1) = -metricEnergy H g := by
    rw [bfgsStep,dot_smul_right]
    simp only [metricEnergy,neg_mul,one_mul]
  have hd : dot g (bfgsStep H g 1) < 0 := by
    rw [he]
    exact neg_neg_of_pos (metricEnergy_pos hH hgn)
  have hL' : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+t • bfgsStep H g 1) := by
    simpa only [← bfgsStep_scaling] using hL
  have hb' : {t : ℝ | 0 < t ∧ ¬ DifferentiableAt ℝ F (x+t • bfgsStep H g 1)}.Finite := by
    simpa only [← bfgsStep_scaling] using hbad
  simpa only [← bfgsStep_scaling] using
    finite_nondifferentiability_step hF x (bfgsStep H g 1) g hg hd hc₁ hc hc₂ L hL' hb'

end BfgsVerification.FiniteRayLineSearch
