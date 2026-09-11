import BfgsVerification.ScalarCounterexamples

/-! Module G's actual infinite accumulating-kink objective. All series and
local polynomial identities are derived from the geometric series. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification.AccumulatingKinks

/-- Index zero corresponds to the source's first knot a_1=1/4. -/
def knot (j : ℕ) : ℝ := (1 / 4 : ℝ) ^ (j + 1)
def term (j : ℕ) (x : ℝ) : ℝ := knot j * max (x - knot j) 0
def kinkSum (x : ℝ) : ℝ := ∑' j, term j x
def objective (x : ℝ) : ℝ := x ^ 2 / 2 + 3 * kinkSum x
def coordinateObjective (x : Vec 1) : ℝ := objective (x 0)

theorem knot_pos (j : ℕ) : 0 < knot j := by unfold knot; positivity
theorem knot_succ (j : ℕ) : knot (j + 1) = knot j / 4 := by unfold knot; rw [pow_succ]; ring
theorem knot_add (j k : ℕ) : knot (k + j) = knot j * (1 / 4 : ℝ) ^ k := by
  unfold knot
  rw [show k + j + 1 = (j + 1) + k by omega, pow_add]

theorem knot_antitone : Antitone knot := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_succ hij)

theorem knot_tendsto : Tendsto knot atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)
  simpa only [knot, pow_succ, zero_mul] using h.mul_const (1 / 4 : ℝ)

theorem knot_summable : Summable knot := by
  have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)
  simpa only [knot, pow_succ] using hs.mul_right (1 / 4 : ℝ)

theorem term_nonneg (j : ℕ) (x : ℝ) : 0 ≤ term j x :=
  mul_nonneg (knot_pos j).le (le_max_right _ _)

theorem term_bound (j : ℕ) (x : ℝ) : term j x ≤ knot j * |x| := by
  apply mul_le_mul_of_nonneg_left _ (knot_pos j).le
  exact max_le (by linarith [le_abs_self x, knot_pos j]) (abs_nonneg x)

theorem term_summable (x : ℝ) : Summable (fun j => term j x) :=
  Summable.of_nonneg_of_le (fun j => term_nonneg j x) (fun j => term_bound j x)
    (knot_summable.mul_right |x|)

/-- The series converges uniformly on every compact set, by an explicit
summable geometric majorant. -/
theorem series_uniform_on_compact {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N x => ∑ j ∈ Finset.range N, term j x) kinkSum atTop K := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  apply tendstoUniformlyOn_tsum_nat (knot_summable.mul_right R)
  intro j x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg j x)]
  exact (term_bound j x).trans (mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using hbound x hx) (knot_pos j).le)

theorem term_convex (j : ℕ) : ConvexOn ℝ univ (term j) := by
  have ha : ConvexOn ℝ univ (fun x : ℝ => x - knot j) := by
    simpa only [Pi.add_apply, id_eq, sub_eq_add_neg] using
      (convexOn_id (𝕜 := ℝ) (β := ℝ) convex_univ).add_const (-knot j)
  simpa only [Pi.sup_apply, smul_eq_mul, term] using
    ConvexOn.smul (knot_pos j).le (ha.sup (convexOn_const 0 convex_univ))

theorem kinkSum_convex : ConvexOn ℝ univ kinkSum := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hle := (term_summable (a * x + b * y)).tsum_le_tsum
    (fun j => (term_convex j).2 hx hy ha hb hab)
    ((term_summable x).mul_left a |>.add ((term_summable y).mul_left b))
  simp only [smul_eq_mul] at hle
  rw [Summable.tsum_add ((term_summable x).mul_left a) ((term_summable y).mul_left b),
    tsum_mul_left, tsum_mul_left] at hle
  exact hle

theorem objective_strongConvex : StrongConvexOn univ 1 objective := by
  rw [strongConvexOn_iff_convex]
  have h := ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 3) kinkSum_convex
  convert h using 1
  ext x
  simp only [objective, Real.norm_eq_abs, sq_abs, smul_eq_mul]
  ring

theorem objective_convex : ConvexOn ℝ univ objective :=
  strongConvexOn_zero.mp (objective_strongConvex.mono (by norm_num : (0 : ℝ) ≤ 1))

theorem objective_lower (x : ℝ) : x ^ 2 / 2 ≤ objective x := by
  have hsum : 0 ≤ kinkSum x := tsum_nonneg (fun j => term_nonneg j x)
  unfold objective
  linarith

@[simp] theorem objective_zero : objective 0 = 0 := by
  have ht : ∀ j, term j 0 = 0 := by
    intro j
    simp only [term, zero_sub, max_eq_right (neg_nonpos.mpr (knot_pos j).le), mul_zero]
  simp [objective, kinkSum, ht]

theorem objective_minimum (x : ℝ) : objective 0 ≤ objective x := by
  rw [objective_zero]
  exact (by positivity : (0 : ℝ) ≤ x ^ 2 / 2).trans (objective_lower x)

theorem objective_unique (x : ℝ) (hx : objective x = objective 0) : x = 0 := by
  have h := objective_lower x
  rw [hx, objective_zero] at h
  nlinarith [sq_nonneg x]

theorem objective_sublevel_compact (b : ℝ) : IsCompact {x | objective x ≤ b} :=
  Localization.sublevel_compact objective_convex 0 objective_minimum objective_unique b

/-- Standard coercivity of the actual infinite-series objective. -/
theorem objective_coercive : Tendsto objective (cocompact ℝ) atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(objective_sublevel_compact b).compl_mem_cocompact] with x hx
  exact le_of_lt (lt_of_not_ge hx)

theorem tail_knots (j : ℕ) : (∑' k, knot (k + j)) = 4 / 3 * knot j := by
  simp only [knot_add, tsum_mul_left]
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)]
  ring

theorem tail_squares (j : ℕ) : (∑' k, (knot (k + j)) ^ 2) = 16 / 15 * (knot j) ^ 2 := by
  have hp (k : ℕ) : ((1 / 4 : ℝ) ^ k) ^ 2 = ((1 / 4 : ℝ) ^ 2) ^ k := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  simp_rw [knot_add, mul_pow, hp]
  rw [tsum_mul_left]
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 4) ^ 2) (by norm_num)]
  ring

theorem tail_knots_summable (j : ℕ) : Summable (fun k => knot (k + j)) :=
  (summable_nat_add_iff j).mpr knot_summable

theorem tail_squares_summable (j : ℕ) : Summable (fun k => (knot (k + j)) ^ 2) := by
  have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 4) ^ 2)
    (by norm_num : (1 / 4 : ℝ) ^ 2 < 1)
  have hp (k : ℕ) : ((1 / 4 : ℝ) ^ k) ^ 2 = ((1 / 4 : ℝ) ^ 2) ^ k := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  convert hs.mul_left ((knot j) ^ 2) using 1
  ext k
  rw [knot_add, mul_pow, hp]

/-- The exact geometric-series value above each knot. Closed endpoints are
included; the term at a shared boundary vanishes. -/
theorem objective_formula_above (j : ℕ) {x : ℝ}
    (hlo : knot j ≤ x) (hhi : x ≤ 4 * knot j) :
    objective x = x ^ 2 / 2 + 4 * knot j * x - 16 / 5 * (knot j) ^ 2 := by
  have hhead : ∑ k ∈ Finset.range j, term k x = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k + 1 ≤ j := Finset.mem_range.mp hk
    have hknot := knot_antitone hkj
    rw [knot_succ] at hknot
    have hxk : x ≤ knot k := by linarith
    simp only [term, max_eq_right (sub_nonpos.mpr hxk), mul_zero]
  have htail : ∀ k, term (k + j) x = knot (k + j) * x - (knot (k + j)) ^ 2 := by
    intro k
    have hxk := (knot_antitone (Nat.le_add_left j k)).trans hlo
    rw [term, max_eq_left (sub_nonneg.mpr hxk)]
    ring
  have hsplit := (term_summable x).sum_add_tsum_nat_add j
  rw [hhead, zero_add] at hsplit
  unfold objective kinkSum
  rw [← hsplit]
  simp_rw [htail]
  rw [Summable.tsum_sub ((tail_knots_summable j).mul_right x) (tail_squares_summable j),
    tsum_mul_right, tail_knots, tail_squares]
  ring

theorem objective_formula_below (j : ℕ) {x : ℝ}
    (hlo : knot j / 4 ≤ x) (hhi : x ≤ knot j) :
    objective x = x ^ 2 / 2 + knot j * x - (knot j) ^ 2 / 5 := by
  have h := objective_formula_above (j + 1) (x := x)
    (by rwa [knot_succ]) (by rw [knot_succ]; linarith)
  rw [knot_succ] at h
  convert h using 1 <;> ring

theorem objective_knot (j : ℕ) : objective (knot j) = 13 / 10 * (knot j) ^ 2 := by
  rw [objective_formula_below j (by nlinarith [knot_pos j]) (le_refl _)]
  ring

theorem polynomial_hasDerivAt (a c x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 / 2 + a * t + c) (x + a) x := by
  convert ((((hasDerivAt_id x).pow 2).div_const 2).add
    ((hasDerivAt_id x).const_mul a)).add_const c using 1 <;> dsimp <;> ring

theorem hasDerivAt_above (j : ℕ) {x : ℝ} (hlo : knot j < x) (hhi : x < 4 * knot j) :
    HasDerivAt objective (x + 4 * knot j) x := by
  apply (polynomial_hasDerivAt (4 * knot j) (-(16 / 5) * (knot j) ^ 2) x).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlo hhi] with t ht
  rw [objective_formula_above j ht.1.le ht.2.le]
  ring

theorem hasDerivAt_below (j : ℕ) {x : ℝ} (hlo : knot j / 4 < x) (hhi : x < knot j) :
    HasDerivAt objective (x + knot j) x := by
  apply (polynomial_hasDerivAt (knot j) (-((knot j) ^ 2 / 5)) x).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlo hhi] with t ht
  rw [objective_formula_below j ht.1.le ht.2.le]
  ring

/-- Exact right derivative 5a at every source knot a. -/
theorem hasDerivWithinAt_knot_right (j : ℕ) :
    HasDerivWithinAt objective (5 * knot j) (Ici (knot j)) (knot j) := by
  have hp := (polynomial_hasDerivAt (4 * knot j) (-(16 / 5) * (knot j) ^ 2) (knot j)).hasDerivWithinAt (s := Ici (knot j))
  have hd : knot j + 4 * knot j = 5 * knot j := by ring
  rw [hd] at hp
  apply hp.congr_of_eventuallyEq ?_ ?_
  · have hu : ∀ᶠ t in 𝓝[Ici (knot j)] (knot j), t < 4 * knot j :=
      (eventually_lt_nhds (by nlinarith [knot_pos j])).filter_mono nhdsWithin_le_nhds
    filter_upwards [hu, self_mem_nhdsWithin] with t ht hlo
    rw [objective_formula_above j hlo ht.le]
    ring
  · rw [objective_formula_above j (le_refl _) (by nlinarith [knot_pos j])]
    ring

/-- Exact left derivative 2a at every source knot a. -/
theorem hasDerivWithinAt_knot_left (j : ℕ) :
    HasDerivWithinAt objective (2 * knot j) (Iic (knot j)) (knot j) := by
  have hp := (polynomial_hasDerivAt (knot j) (-((knot j) ^ 2 / 5)) (knot j)).hasDerivWithinAt (s := Iic (knot j))
  have hd : knot j + knot j = 2 * knot j := by ring
  rw [hd] at hp
  apply hp.congr_of_eventuallyEq ?_ ?_
  · have hl : ∀ᶠ t in 𝓝[Iic (knot j)] (knot j), knot j / 4 < t :=
      (eventually_gt_nhds (by nlinarith [knot_pos j])).filter_mono nhdsWithin_le_nhds
    filter_upwards [hl, self_mem_nhdsWithin] with t ht hhi
    rw [objective_formula_below j ht.le hhi]
    ring
  · rw [objective_formula_below j (by nlinarith [knot_pos j]) (le_refl _)]
    ring

theorem not_differentiableAt_knot (j : ℕ) : ¬ DifferentiableAt ℝ objective (knot j) := by
  intro h
  have hr := (uniqueDiffOn_Ici (knot j) (knot j) (by simp)).eq_deriv _
    (hasDerivWithinAt_knot_right j) h.hasDerivAt.hasDerivWithinAt
  have hl := (uniqueDiffOn_Iic (knot j) (knot j) (by simp)).eq_deriv _
    (hasDerivWithinAt_knot_left j) h.hasDerivAt.hasDerivWithinAt
  nlinarith [knot_pos j]

theorem objective_nonpos {x : ℝ} (hx : x ≤ 0) : objective x = x ^ 2 / 2 := by
  have ht : ∀ j, term j x = 0 := by
    intro j
    have h : x - knot j ≤ 0 := by linarith [knot_pos j]
    simp only [term, max_eq_right h, mul_zero]
  simp [objective, kinkSum, ht]

theorem objective_quadratic_upper {x : ℝ} (hx : |x| ≤ 1) : objective x ≤ 9 / 2 * x ^ 2 := by
  by_cases hp : 0 < x
  · have hx1 : x ≤ 1 := (le_abs_self x).trans hx
    obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one hp hx1
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    have hlo : knot j < x := hjlo
    have hhi : x ≤ 4 * knot j := by
      have he : 4 * knot j = (1 / 4 : ℝ) ^ j := by unfold knot; rw [pow_succ]; ring
      rwa [he]
    rw [objective_formula_above j hlo.le hhi]
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hlo.le), sq_nonneg (knot j)]
  · rw [objective_nonpos (le_of_not_gt hp)]
    nlinarith [sq_nonneg x]

/-- The minimizer is differentiable even though nonsmooth knots accumulate
at it. This follows from a proved quadratic upper bound for the actual series. -/
theorem hasDerivAt_zero : HasDerivAt objective 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [objective_zero, sub_zero, smul_zero, Real.norm_eq_abs]
  have hupper : ∀ᶠ x : ℝ in 𝓝 0, |x|⁻¹ * |objective x| ≤ (9 / 2 : ℝ) * |x| := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with x hx
    have habs : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have hnonneg : 0 ≤ objective x := by simpa using objective_minimum x
    rw [abs_of_nonneg hnonneg]
    calc
      _ ≤ |x|⁻¹ * (9 / 2 * x ^ 2) := mul_le_mul_of_nonneg_left
        (objective_quadratic_upper habs) (inv_nonneg.mpr (abs_nonneg x))
      _ = (9 / 2 : ℝ) * |x| := by
        by_cases hz : x = 0
        · simp [hz]
        · rw [← sq_abs x]
          field_simp [abs_ne_zero.mpr hz]
          nlinarith [sq_abs x]
  apply squeeze_zero' (Eventually.of_forall (fun x => mul_nonneg
    (inv_nonneg.mpr (abs_nonneg x)) (abs_nonneg _))) hupper
  simpa using ((continuous_abs.tendsto (0 : ℝ)).const_mul (9 / 2 : ℝ))

open OneDimensional TransportedCertificate

theorem coordinateObjective_convex : ConvexOn ℝ univ coordinateObjective := by
  simpa only [Set.preimage_univ, Function.comp_def, coordinateObjective] using
    objective_convex.comp_linearMap
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).toLinearMap

@[simp] theorem coordinateObjective_zero : coordinateObjective 0 = 0 := objective_zero

theorem coordinateObjective_minimum (x : Vec 1) : coordinateObjective 0 ≤ coordinateObjective x :=
  objective_minimum (x 0)

theorem coordinateObjective_unique (x : Vec 1)
    (h : coordinateObjective x = coordinateObjective 0) : x = 0 := by
  have he : x 0 = 0 := objective_unique (x 0) h
  rw [← embed_eval x, he]
  rfl

theorem coordinateObjective_sublevel_compact (b : ℝ) :
    IsCompact {x | coordinateObjective x ≤ b} :=
  Localization.sublevel_compact coordinateObjective_convex 0
    coordinateObjective_minimum coordinateObjective_unique b

def crossingX (j : ℕ) (ε : ℝ) : Vec 1 := embed (knot j + ε)
def crossingZ (j : ℕ) (ε : ℝ) : Vec 1 := embed (knot j - ε)
def crossingG (j : ℕ) (ε : ℝ) : Vec 1 := embed (5 * knot j + ε)
def crossingH (j : ℕ) (ε : ℝ) : Vec 1 := embed (2 * knot j - ε)

theorem crossing_gradients (j : ℕ) {ε : ℝ} (hε : 0 < ε) (hs : ε ≤ knot j / 8) :
    HasFDerivAt coordinateObjective (gradientFunctional (crossingG j ε)) (crossingX j ε) ∧
    HasFDerivAt coordinateObjective (gradientFunctional (crossingH j ε)) (crossingZ j ε) := by
  have hdx := hasDerivAt_above j (x := knot j + ε) (by linarith) (by nlinarith [knot_pos j])
  have hdz := hasDerivAt_below j (x := knot j - ε) (by nlinarith [knot_pos j]) (by linarith)
  have hgx : knot j + ε + 4 * knot j = 5 * knot j + ε := by ring
  have hgz : knot j - ε + knot j = 2 * knot j - ε := by ring
  rw [hgx] at hdx
  rw [hgz] at hdz
  exact ⟨ScalarCounterexamples.coordinate_hasGradient hdx, ScalarCounterexamples.coordinate_hasGradient hdz⟩

theorem crossing_values (j : ℕ) {ε : ℝ} (hε : 0 < ε) (hs : ε ≤ knot j / 8) :
    coordinateObjective (crossingX j ε) = 13 / 10 * (knot j) ^ 2 + 5 * knot j * ε + ε ^ 2 / 2 ∧
    coordinateObjective (crossingZ j ε) = 13 / 10 * (knot j) ^ 2 - 2 * knot j * ε + ε ^ 2 / 2 := by
  constructor
  · change objective (knot j + ε) = _
    rw [objective_formula_above j (by linarith) (by nlinarith [knot_pos j])]
    ring
  · change objective (knot j - ε) = _
    rw [objective_formula_below j (by nlinarith [knot_pos j]) (by linarith)]
    ring

theorem crossing_decrease (j : ℕ) (ε : ℝ) :
    pairDecrease (crossingX j ε) (crossingZ j ε) (crossingG j ε) = 10 * knot j * ε + 2 * ε ^ 2 := by
  simp [pairDecrease, pairStep, crossingX, crossingZ, crossingG, dot]
  ring

theorem crossing_curvature (j : ℕ) (ε : ℝ) :
    pairCurvature (crossingX j ε) (crossingZ j ε) (crossingG j ε) (crossingH j ε) =
      6 * knot j * ε + 4 * ε ^ 2 := by
  simp [pairCurvature, pairStep, crossingX, crossingZ, crossingG, crossingH, dot]
  ring

theorem crossing_strict (j : ℕ) {ε : ℝ} (hε : 0 < ε) (hs : ε ≤ knot j / 8) :
    0 < pairDecrease (crossingX j ε) (crossingZ j ε) (crossingG j ε) ∧
    (1 / 4 : ℝ) * pairDecrease (crossingX j ε) (crossingZ j ε) (crossingG j ε) <
      coordinateObjective (crossingX j ε) - coordinateObjective (crossingZ j ε) ∧
    coordinateObjective (crossingX j ε) - coordinateObjective (crossingZ j ε) <
      pairDecrease (crossingX j ε) (crossingZ j ε) (crossingG j ε) ∧
    (1 - (1 / 2 : ℝ)) * pairDecrease (crossingX j ε) (crossingZ j ε) (crossingG j ε) <
      pairCurvature (crossingX j ε) (crossingZ j ε) (crossingG j ε) (crossingH j ε) := by
  rw [crossing_decrease, crossing_curvature, (crossing_values j hε hs).1, (crossing_values j hε hs).2]
  have hap : 0 < knot j * ε := mul_pos (knot_pos j) hε
  have hes : ε ^ 2 ≤ knot j * ε / 8 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hs)]
  constructor
  · nlinarith [sq_nonneg ε]
  constructor
  · nlinarith
  constructor <;> nlinarith [sq_nonneg ε]

theorem crossing_eligible (j : ℕ) {ε : ℝ} (hε : 0 < ε) (hs : ε ≤ knot j / 8) :
    EligiblePair coordinateObjective (1 / 4) (1 / 2)
      (crossingX j ε) (crossingZ j ε) (crossingG j ε) (crossingH j ε) where
  gradient_x := (crossing_gradients j hε hs).1
  gradient_z := (crossing_gradients j hε hs).2
  decrease_pos := (crossing_strict j hε hs).1
  armijo := (crossing_strict j hε hs).2.1.le
  convex_decrease := (crossing_strict j hε hs).2.2.1.le
  curvature := (crossing_strict j hε hs).2.2.2.le

def bandGap (j : ℕ) : ℝ := 13 / 20 * (knot j) ^ 2

theorem bandGap_pos (j : ℕ) : 0 < bandGap j := by
  have h := knot_pos j
  unfold bandGap
  positivity

theorem crossing_lower_band (j : ℕ) {ε : ℝ} (hε : 0 < ε) (hs : ε ≤ knot j / 8) :
    bandGap j ≤ coordinateObjective (crossingX j ε) ∧
    bandGap j ≤ coordinateObjective (crossingZ j ε) := by
  rw [(crossing_values j hε hs).1, (crossing_values j hε hs).2]
  unfold bandGap
  have hp : 0 ≤ knot j * ε := mul_nonneg (knot_pos j).le hε.le
  have he : knot j * ε ≤ (knot j) ^ 2 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (knot_pos j).le]
  constructor <;> nlinarith [sq_nonneg (knot j), sq_nonneg ε]

def crossingScale (j k : ℕ) : ℝ := knot j * ScalarCounterexamples.crossingScale k

theorem crossingScale_pos (j k : ℕ) : 0 < crossingScale j k :=
  mul_pos (knot_pos j) (ScalarCounterexamples.crossingScale_pos k)

theorem crossingScale_le (j k : ℕ) : crossingScale j k ≤ knot j / 8 := by
  have h := mul_le_mul_of_nonneg_left (ScalarCounterexamples.crossingScale_le k) (knot_pos j).le
  simpa only [crossingScale, div_eq_mul_inv, one_mul] using h

theorem crossingScale_tendsto (j : ℕ) : Tendsto (crossingScale j) atTop (𝓝 0) := by
  simpa only [crossingScale, mul_zero] using ScalarCounterexamples.crossingScale_tendsto.const_mul (knot j)

theorem crossing_decrease_tendsto (j : ℕ) :
    Tendsto (fun k => pairDecrease (crossingX j (crossingScale j k))
      (crossingZ j (crossingScale j k)) (crossingG j (crossingScale j k))) atTop (𝓝 0) := by
  simpa only [crossing_decrease, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
    ((crossingScale_tendsto j).const_mul (10 * knot j)).add
      (((crossingScale_tendsto j).pow 2).const_mul (2 : ℝ))

theorem crossingX_tendsto (j : ℕ) :
    Tendsto (fun k => crossingX j (crossingScale j k)) atTop (𝓝 (embed (knot j))) := by
  simpa only [crossingX, add_zero] using embed.continuous.continuousAt.tendsto.comp
    ((crossingScale_tendsto j).const_add (knot j))

theorem crossingZ_tendsto (j : ℕ) :
    Tendsto (fun k => crossingZ j (crossingScale j k)) atTop (𝓝 (embed (knot j))) := by
  simpa only [crossingZ, sub_zero] using embed.continuous.continuousAt.tendsto.comp
    ((crossingScale_tendsto j).const_sub (knot j))

theorem crossing_quotient (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    |crossingH j ε 0 - crossingG j ε 0| /
      (|crossingZ j ε 0 - crossingX j ε 0| * (crossingH j ε 0) ^ 2) =
      (3 * knot j + 2 * ε) / (2 * ε * (2 * knot j - ε) ^ 2) := by
  have hy : 2 * knot j - ε - (5 * knot j + ε) < 0 := by nlinarith [knot_pos j]
  have hs : knot j - ε - (knot j + ε) < 0 := by linarith
  simp only [crossingH, crossingG, crossingZ, crossingX, embed_apply,
    abs_of_neg hy, abs_of_neg hs]
  congr 1 <;> ring

/-- The exact source quotient tends to positive infinity at a fixed knot. -/
theorem crossing_quotient_tendsto (j : ℕ) :
    Tendsto (fun ε => |crossingH j ε 0 - crossingG j ε 0| /
      (|crossingZ j ε 0 - crossingX j ε 0| * (crossingH j ε 0) ^ 2)) (𝓝[>] 0) atTop := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hn : Tendsto (fun ε : ℝ => 3 * knot j + 2 * ε) (𝓝[>] 0) (𝓝 (3 * knot j)) := by
    simpa using (he.const_mul (2 : ℝ)).const_add (3 * knot j)
  have hd : Tendsto (fun ε : ℝ => 2 * ε * (2 * knot j - ε) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (he.const_mul (2 : ℝ)).mul ((he.const_sub (2 * knot j)).pow 2)
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < 2 * ε * (2 * knot j - ε) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (knot_pos j)).filter_mono nhdsWithin_le_nhds] with ε hε hsmall
    have hh : 0 < 2 * knot j - ε := by nlinarith [knot_pos j]
    exact mul_pos (mul_pos (by norm_num) hε) (sq_pos_of_pos hh)
  apply (ScalarCounterexamples.ratio_tendsto_atTop (mul_pos (by norm_num) (knot_pos j)) hn hd hp).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (crossing_quotient j hε).symm

/-- Fixing one knot first gives failure of the quotient bound on its one
fixed positive band, for every threshold and every finite constant. -/
theorem no_quotient_near_knot (j : ℕ) {K : Set (Vec 1)}
    (hK : K ∈ 𝓝 (embed (knot j))) :
    ¬ ScalarQuotientBound coordinateObjective K 0 (1 / 4) (1 / 2) (bandGap j) := by
  rintro ⟨δ, hδ, A, hA⟩
  have hXK := (crossingX_tendsto j).eventually hK
  have hZK := (crossingZ_tendsto j).eventually hK
  have hsmall : ∀ᶠ k in atTop, pairDecrease (crossingX j (crossingScale j k))
      (crossingZ j (crossingScale j k)) (crossingG j (crossingScale j k)) ≤ δ :=
    ((crossing_decrease_tendsto j).eventually (eventually_lt_nhds hδ)).mono (fun _ h => h.le)
  have hbound : ∀ᶠ k in atTop, 3 * knot j ≤
      A * (2 * crossingScale j k * (2 * knot j - crossingScale j k) ^ 2) := by
    filter_upwards [hXK, hZK, hsmall] with k hx hz hd
    have hε := crossingScale_pos j k
    have hs := crossingScale_le j k
    have hb := crossing_lower_band j hε hs
    have hxb : crossingX j (crossingScale j k) ∈ positiveBand coordinateObjective K 0 (bandGap j) :=
      ⟨hx, by simpa only [zero_add] using hb.1⟩
    have hzb : crossingZ j (crossingScale j k) ∈ positiveBand coordinateObjective K 0 (bandGap j) :=
      ⟨hz, by simpa only [zero_add] using hb.2⟩
    have he := hA _ _ _ _ hxb hzb (crossing_eligible j hε hs) hd
    have hy : 2 * knot j - crossingScale j k - (5 * knot j + crossingScale j k) < 0 := by
      nlinarith [knot_pos j]
    have hst : knot j - crossingScale j k - (knot j + crossingScale j k) < 0 := by linarith
    simp only [crossingX, crossingZ, crossingG, crossingH, embed_apply,
      abs_of_neg hy, abs_of_neg hst] at he
    have hh : 0 < 2 * knot j - crossingScale j k := by nlinarith [knot_pos j]
    have hden : 0 < -(knot j - crossingScale j k - (knot j + crossingScale j k)) *
        (2 * knot j - crossingScale j k) ^ 2 := mul_pos (neg_pos.mpr hst) (sq_pos_of_pos hh)
    have hm := (div_le_iff₀ hden).mp he
    nlinarith
  have hlim : Tendsto (fun k => A * (2 * crossingScale j k *
      (2 * knot j - crossingScale j k) ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero, zero_mul] using
      (((crossingScale_tendsto j).const_mul (2 : ℝ)).mul
        (((crossingScale_tendsto j).const_sub (2 * knot j)).pow 2)).const_mul A
  have hfalse : 3 * knot j ≤ 0 := ge_of_tendsto hlim hbound
  nlinarith [knot_pos j]

/-- Suppression and visibility alone already fail near a fixed knot. -/
theorem no_visibility_secant_near_knot (j : ℕ) {K : Set (Vec 1)}
    (hK : K ∈ 𝓝 (embed (knot j))) :
    ¬ Nonempty (VisibilitySecantCertificate coordinateObjective K 0 (1 / 4) (1 / 2) (bandGap j)) := by
  rintro ⟨B⟩
  exact no_quotient_near_knot j hK (quotient_bound_of_visibility_secant (by norm_num) B)

theorem no_band_certificate_near_knot (j : ℕ) {K : Set (Vec 1)}
    (hK : K ∈ 𝓝 (embed (knot j))) :
    ¬ Nonempty (BandCertificate coordinateObjective K 0 (1 / 4) (1 / 2) (bandGap j)) := by
  rintro ⟨B⟩
  exact no_visibility_secant_near_knot j hK ⟨B.toVisibilitySecant⟩

/-- Every neighborhood of the minimizer contains a fixed knot with its own
neighborhood inside that set. No uniformity in the knot index is assumed. -/
theorem exists_knot_interior {K : Set (Vec 1)} (hK : K ∈ 𝓝 (0 : Vec 1)) :
    ∃ j, K ∈ 𝓝 (embed (knot j)) := by
  obtain ⟨U, hUK, hU, hzero⟩ := mem_nhds_iff.mp hK
  have ht : Tendsto (fun j => embed (knot j)) atTop (𝓝 (0 : Vec 1)) := by
    simpa using embed.continuous.continuousAt.tendsto.comp knot_tendsto
  obtain ⟨j, hj⟩ := (ht.eventually (hU.mem_nhds hzero)).exists
  exact ⟨j, Filter.mem_of_superset (hU.mem_nhds hj) hUK⟩

/-- Exact local nonnecessity: on every neighborhood of zero the all-positive-
band transported certificate condition fails, although every scalar run converges. -/
theorem every_neighborhood_no_certificates {K : Set (Vec 1)} (hK : K ∈ 𝓝 (0 : Vec 1)) :
    ¬ HasBandCertificates coordinateObjective K 0 (1 / 4) (1 / 2) := by
  obtain ⟨j, hj⟩ := exists_knot_interior hK
  intro h
  apply no_band_certificate_near_knot j hj
  apply h (bandGap j) (bandGap_pos j)
  refine ⟨embed (knot j), mem_of_mem_nhds hj, ?_⟩
  change 0 + bandGap j ≤ objective (knot j)
  rw [objective_knot]
  unfold bandGap
  nlinarith [sq_nonneg (knot j)]

theorem nonsmooth_in_every_neighborhood {U : Set ℝ} (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ x ∈ U, ¬ DifferentiableAt ℝ objective x := by
  obtain ⟨j, hj⟩ := (knot_tendsto.eventually hU).exists
  exact ⟨knot j, hj, not_differentiableAt_knot j⟩

/-- Every arbitrary positive-metric scalar run converges globally to zero;
compactness of its initial sublevel is supplied by the actual objective. -/
theorem scalar_run_converges (R : ScalarMetricRun objective) :
    Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hK : IsCompact R.initialSublevel := objective_sublevel_compact _
  simpa only [objective_zero] using R.convergence hK 0 objective_minimum objective_unique

theorem actual_bfgs_converges (R : AdmissibleBFGSRun 1 coordinateObjective) :
    Tendsto (fun k => coordinateObjective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) := by
  have hK : IsCompact R.initialSublevel := coordinateObjective_sublevel_compact _
  simpa only [coordinateObjective_zero] using R.scalar_convergence hK 0
    coordinateObjective_minimum coordinateObjective_unique

end BfgsVerification.AccumulatingKinks
