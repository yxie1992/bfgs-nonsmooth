import BfgsVerification.ScalarCertificate

/-! Module G's shifted-quadratic example: convergence of every scalar run,
but no transported certificate on a fixed compact positive band. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix

namespace BfgsVerification.ScalarCounterexamples
open TransportedCertificate OneDimensional

def shiftedAbs (t : ℝ) : ℝ := (t + 2) ^ 2 / 2 + |t|

def shiftedObjective (x : Vec 1) : ℝ := shiftedAbs (x 0)

theorem shiftedAbs_strongConvex : StrongConvexOn univ 1 shiftedAbs := by
  rw [strongConvexOn_iff_convex]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hnorm : |a * x + b * y| ≤ a * |x| + b * |y| := by
    calc
      _ ≤ |a * x| + |b * y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  simp only [shiftedAbs, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  have hb' : b = 1 - a := by linarith
  rw [hb'] at hnorm ⊢
  nlinarith

theorem shiftedAbs_convex : ConvexOn ℝ univ shiftedAbs :=
  strongConvexOn_zero.mp (shiftedAbs_strongConvex.mono (by norm_num : (0 : ℝ) ≤ 1))

theorem shiftedObjective_convex : ConvexOn ℝ univ shiftedObjective := by
  simpa only [Set.preimage_univ, Function.comp_def, shiftedObjective] using
    shiftedAbs_convex.comp_linearMap (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).toLinearMap

theorem shiftedAbs_gap_lower (t : ℝ) : (t + 1) ^ 2 / 2 + 3 / 2 ≤ shiftedAbs t := by
  have h := neg_le_abs t
  unfold shiftedAbs
  nlinarith

theorem shiftedAbs_minimum (t : ℝ) : shiftedAbs (-1) ≤ shiftedAbs t := by
  have h := shiftedAbs_gap_lower t
  norm_num [shiftedAbs] at *
  nlinarith [sq_nonneg (t + 1)]

theorem shiftedAbs_unique (t : ℝ) (h : shiftedAbs t = shiftedAbs (-1)) : t = -1 := by
  have hb := shiftedAbs_gap_lower t
  have hval : shiftedAbs (-1) = 3 / 2 := by norm_num [shiftedAbs]
  rw [hval] at h
  rw [h] at hb
  nlinarith [sq_nonneg (t + 1)]

theorem shiftedAbs_sublevel_compact (b : ℝ) : IsCompact {t | shiftedAbs t ≤ b} :=
  Localization.sublevel_compact shiftedAbs_convex (-1) shiftedAbs_minimum shiftedAbs_unique b

theorem shiftedObjective_minimum (x : Vec 1) : shiftedObjective (embed (-1)) ≤ shiftedObjective x :=
  shiftedAbs_minimum (x 0)

theorem shiftedObjective_unique (x : Vec 1)
    (h : shiftedObjective x = shiftedObjective (embed (-1))) : x = embed (-1) := by
  have he : x 0 = -1 := shiftedAbs_unique (x 0) h
  rw [← embed_eval x, he]

theorem shiftedObjective_sublevel_compact (b : ℝ) : IsCompact {x | shiftedObjective x ≤ b} :=
  Localization.sublevel_compact shiftedObjective_convex (embed (-1))
    shiftedObjective_minimum shiftedObjective_unique b

theorem shiftedAbs_hasDerivAt_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt shiftedAbs (t + 3) t := by
  convert ((((hasDerivAt_id t).add_const 2).pow 2).div_const 2).add
    (hasDerivAt_abs_pos ht) using 1 <;> dsimp [shiftedAbs] <;> ring

theorem shiftedAbs_hasDerivAt_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt shiftedAbs (t + 1) t := by
  convert ((((hasDerivAt_id t).add_const 2).pow 2).div_const 2).add
    (hasDerivAt_abs_neg ht) using 1 <;> dsimp [shiftedAbs] <;> ring

/-- A scalar derivative supplies the exact coordinate gradient in dimension one. -/
theorem coordinate_hasGradient {f : ℝ → ℝ} {t a : ℝ} (h : HasDerivAt f a t) :
    HasFDerivAt (fun x : Vec 1 => f (x 0)) (gradientFunctional (embed a)) (embed t) := by
  have hp : HasFDerivAt (fun x : Vec 1 => x 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) (embed t) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  convert h.comp_hasFDerivAt (embed t) hp using 1
  ext v
  simp [gradientFunctional_apply, dot]

def crossingX (ε : ℝ) : Vec 1 := embed ε
def crossingZ (ε : ℝ) : Vec 1 := embed (-ε / 2)
def crossingG (ε : ℝ) : Vec 1 := embed (3 + ε)
def crossingH (ε : ℝ) : Vec 1 := embed (1 - ε / 2)

theorem crossing_gradients {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt shiftedObjective (gradientFunctional (crossingG ε)) (crossingX ε) ∧
    HasFDerivAt shiftedObjective (gradientFunctional (crossingH ε)) (crossingZ ε) := by
  constructor
  · simpa only [shiftedObjective, crossingG, crossingX, add_comm] using
      coordinate_hasGradient (shiftedAbs_hasDerivAt_pos hε)
  · have hn : -ε / 2 < 0 := by linarith
    simpa only [shiftedObjective, crossingH, crossingZ, sub_eq_add_neg, neg_div, add_comm] using
      coordinate_hasGradient (shiftedAbs_hasDerivAt_neg hn)

theorem crossing_values {ε : ℝ} (hε : 0 < ε) :
    shiftedObjective (crossingX ε) = 2 + 3 * ε + ε ^ 2 / 2 ∧
    shiftedObjective (crossingZ ε) = 2 - ε / 2 + ε ^ 2 / 8 := by
  constructor
  · simp only [shiftedObjective, crossingX, embed_apply, shiftedAbs, abs_of_pos hε]
    ring
  · have hn : -ε / 2 < 0 := by linarith
    simp only [shiftedObjective, crossingZ, embed_apply, shiftedAbs, abs_of_neg hn]
    ring

theorem crossing_decrease (ε : ℝ) :
    pairDecrease (crossingX ε) (crossingZ ε) (crossingG ε) =
      9 / 2 * ε + 3 / 2 * ε ^ 2 := by
  simp [pairDecrease, pairStep, crossingX, crossingZ, crossingG, dot]
  ring

theorem crossing_curvature (ε : ℝ) :
    pairCurvature (crossingX ε) (crossingZ ε) (crossingG ε) (crossingH ε) =
      3 * ε + 9 / 4 * ε ^ 2 := by
  simp [pairCurvature, pairStep, crossingX, crossingZ, crossingG, crossingH, dot]
  ring

/-- The exact source small crossing is eligible for (1/4,1/2); all relevant
acceptance comparisons are strict. -/
theorem crossing_strict {ε : ℝ} (hε : 0 < ε) :
    0 < pairDecrease (crossingX ε) (crossingZ ε) (crossingG ε) ∧
    (1 / 4 : ℝ) * pairDecrease (crossingX ε) (crossingZ ε) (crossingG ε) <
      shiftedObjective (crossingX ε) - shiftedObjective (crossingZ ε) ∧
    shiftedObjective (crossingX ε) - shiftedObjective (crossingZ ε) <
      pairDecrease (crossingX ε) (crossingZ ε) (crossingG ε) ∧
    (1 - (1 / 2 : ℝ)) * pairDecrease (crossingX ε) (crossingZ ε) (crossingG ε) <
      pairCurvature (crossingX ε) (crossingZ ε) (crossingG ε) (crossingH ε) := by
  rw [crossing_decrease, crossing_curvature, (crossing_values hε).1, (crossing_values hε).2]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith [sq_nonneg ε]

theorem crossing_eligible {ε : ℝ} (hε : 0 < ε) :
    EligiblePair shiftedObjective (1 / 4) (1 / 2)
      (crossingX ε) (crossingZ ε) (crossingG ε) (crossingH ε) where
  gradient_x := (crossing_gradients hε).1
  gradient_z := (crossing_gradients hε).2
  decrease_pos := (crossing_strict hε).1
  armijo := (crossing_strict hε).2.1.le
  convex_decrease := (crossing_strict hε).2.2.1.le
  curvature := (crossing_strict hε).2.2.2.le

theorem crossing_band {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 8) :
    crossingX ε ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1 / 4) ∧
    crossingZ ε ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1 / 4) := by
  have hm : shiftedObjective (embed (-1)) = 3 / 2 := by norm_num [shiftedObjective, shiftedAbs]
  have hv := crossing_values hε
  simp only [positiveBand, Set.mem_setOf_eq]
  rw [hm, hv.1, hv.2]
  have he2 : ε ^ 2 ≤ ε / 8 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hsmall)]
  constructor <;> constructor <;> nlinarith [sq_nonneg ε]

/-- A specific positive sequence staying inside the source small-pair regime. -/
def crossingScale (k : ℕ) : ℝ := (1 / 8) * (1 / ((k : ℝ) + 1))

theorem crossingScale_pos (k : ℕ) : 0 < crossingScale k := by unfold crossingScale; positivity

theorem crossingScale_le (k : ℕ) : crossingScale k ≤ 1 / 8 := by
  unfold crossingScale
  have h : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hd : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr h
  nlinarith

theorem crossingScale_tendsto : Tendsto crossingScale atTop (𝓝 0) := by
  simpa only [crossingScale, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 8 : ℝ)

theorem crossing_decrease_tendsto :
    Tendsto (fun k => pairDecrease (crossingX (crossingScale k))
      (crossingZ (crossingScale k)) (crossingG (crossingScale k))) atTop (𝓝 0) := by
  simpa only [crossing_decrease, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
    (crossingScale_tendsto.const_mul (9 / 2 : ℝ)).add
      ((crossingScale_tendsto.pow 2).const_mul (3 / 2 : ℝ))

/-- A positive limiting numerator divided by a positive denominator tending
to zero has the literal divergence claimed in the source examples. -/
theorem ratio_tendsto_atTop {ι : Type*} {l : Filter ι} {f g : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < g i) : Tendsto (fun i => f i / g i) l atTop := by
  have hgt : Tendsto g l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hg, hpos⟩
  simpa only [div_eq_mul_inv] using hf.pos_mul_atTop hc hgt.inv_tendsto_nhdsGT_zero

theorem crossing_quotient {ε : ℝ} (hε : 0 < ε) :
    |crossingH ε 0 - crossingG ε 0| /
      (|crossingZ ε 0 - crossingX ε 0| * (crossingH ε 0) ^ 2) =
      (2 + 3 / 2 * ε) / (3 / 2 * ε * (1 - ε / 2) ^ 2) := by
  have hy : 1 - ε / 2 - (3 + ε) < 0 := by linarith
  have hs : -ε / 2 - ε < 0 := by linarith
  simp only [crossingH, crossingG, crossingZ, crossingX, embed_apply,
    abs_of_neg hy, abs_of_neg hs]
  congr 1 <;> ring

theorem crossing_quotient_tendsto :
    Tendsto (fun ε => |crossingH ε 0 - crossingG ε 0| /
      (|crossingZ ε 0 - crossingX ε 0| * (crossingH ε 0) ^ 2)) (𝓝[>] 0) atTop := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hn : Tendsto (fun ε : ℝ => 2 + 3 / 2 * ε) (𝓝[>] 0) (𝓝 2) := by
    simpa using (he.const_mul (3 / 2 : ℝ)).const_add 2
  have hd : Tendsto (fun ε : ℝ => 3 / 2 * ε * (1 - ε / 2) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (he.const_mul (3 / 2 : ℝ)).mul (((he.div_const 2).const_sub 1).pow 2)
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < 3 / 2 * ε * (1 - ε / 2) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with ε hε hsmall
    have hh : 0 < 1 - ε / 2 := by linarith
    exact mul_pos (mul_pos (by norm_num) hε) (sq_pos_of_pos hh)
  apply (ratio_tendsto_atTop (by norm_num) hn hd hp).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (crossing_quotient hε).symm

/-- Concrete small eligible crossings violate every possible uniform eligible
Lipschitz constant, with the band and its threshold quantifiers unchanged. -/
theorem shifted_not_eligible_lipschitz :
    ¬ ScalarEligibleLipschitz shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) (1 / 4) := by
  rintro ⟨δ, hδ, A, hA⟩
  have hsmall : ∀ᶠ k in atTop, pairDecrease (crossingX (crossingScale k))
      (crossingZ (crossingScale k)) (crossingG (crossingScale k)) ≤ δ :=
    (crossing_decrease_tendsto.eventually (eventually_lt_nhds hδ)).mono (fun _ h => h.le)
  have hbound : ∀ᶠ k in atTop, (2 : ℝ) ≤ A * (3 / 2 * crossingScale k) := by
    filter_upwards [hsmall] with k hk
    have hε := crossingScale_pos k
    have hb := crossing_band hε (crossingScale_le k)
    have he := hA _ _ _ _ hb.1 hb.2 (crossing_eligible hε) hk
    have hy : 1 - crossingScale k / 2 - (3 + crossingScale k) < 0 := by linarith
    have hs : -crossingScale k / 2 - crossingScale k < 0 := by linarith
    simp only [crossingX, crossingZ, crossingG, crossingH, embed_apply,
      abs_of_neg hy, abs_of_neg hs] at he
    nlinarith
  have hlim : Tendsto (fun k => A * (3 / 2 * crossingScale k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (crossingScale_tendsto.const_mul (3 / 2 : ℝ)).const_mul A
  have hfalse : (2 : ℝ) ≤ 0 := ge_of_tendsto hlim hbound
  norm_num at hfalse

theorem shifted_no_band_certificate :
    ¬ Nonempty (BandCertificate shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) (1 / 4)) := by
  intro h
  apply shifted_not_eligible_lipschitz
  exact (scalar_certificate_iff_eligible_lipschitz shiftedObjective_convex (embed (-1))
    (shiftedObjective_sublevel_compact 3) (by norm_num) (by norm_num)).mp h

theorem shifted_no_band_certificates :
    ¬ HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) := by
  intro h
  apply shifted_no_band_certificate
  exact h (1 / 4) (by norm_num)
    ⟨crossingX (crossingScale 0), (crossing_band (crossingScale_pos 0) (crossingScale_le 0)).1⟩

/-- All positive-metric scalar runs converge on this objective despite the
proved certificate nonexistence. Compactness is derived, not assumed. -/
theorem shifted_scalar_run_converges (R : ScalarMetricRun shiftedAbs) :
    Tendsto (fun k => shiftedAbs (R.x k)) atTop (𝓝 (3 / 2)) ∧
      Tendsto R.x atTop (𝓝 (-1)) := by
  have hK : IsCompact R.initialSublevel := shiftedAbs_sublevel_compact _
  have hv : shiftedAbs (-1) = 3 / 2 := by norm_num [shiftedAbs]
  simpa only [hv] using R.convergence hK (-1) shiftedAbs_minimum shiftedAbs_unique

theorem shifted_actual_bfgs_converges (R : AdmissibleBFGSRun 1 shiftedObjective) :
    Tendsto (fun k => shiftedObjective (R.x k)) atTop (𝓝 (3 / 2)) ∧
      Tendsto R.x atTop (𝓝 (embed (-1))) := by
  have hK : IsCompact R.initialSublevel := shiftedObjective_sublevel_compact _
  have hv : shiftedObjective (embed (-1)) = 3 / 2 := by norm_num [shiftedObjective, shiftedAbs]
  simpa only [hv] using R.scalar_convergence hK (embed (-1))
    shiftedObjective_minimum shiftedObjective_unique

end BfgsVerification.ScalarCounterexamples
