import BfgsVerification.NormalSpikeTargets

section
open scoped Topology
open Set Filter
namespace BfgsVerification.NormalSpike

def ratScale (N : ℕ) : ℚ := (1/2 : ℚ)^(N+2)
def ratMassPoly (t : ℚ) : ℚ := t-(2/3 : ℚ)*t^3+(1/5 : ℚ)*t^5
def ratMomentPoly (t : ℚ) : ℚ := (1/2 : ℚ)*t^2-(1/2 : ℚ)*t^4+(1/6 : ℚ)*t^6
def ratCumulativeMass (t : ℚ) : ℚ := if t ≤ -1 then 0 else if t ≤ 1 then ratMassPoly t+8/15 else 16/15
def ratPrimitive (t : ℚ) : ℚ := if t ≤ -1 then 0 else if t ≤ 1 then
  t*(ratMassPoly t+8/15)-ratMomentPoly t+1/6 else (16/15)*t
def ratScaledPrimitive (a v : ℚ) : ℚ := a^7*ratPrimitive ((v-a)/a^5)
def ratScaledMass (a v : ℚ) : ℚ := a^2*ratCumulativeMass ((v-a)/a^5)

theorem ratScale_cast (N : ℕ) : (ratScale N : ℝ) = scale N := by
  simp [ratScale, scale]

theorem ratMassPoly_cast (t : ℚ) : (ratMassPoly t : ℝ) = massPoly t := by
  simp [ratMassPoly, massPoly]

theorem ratMomentPoly_cast (t : ℚ) : (ratMomentPoly t : ℝ) = momentPoly t := by
  simp [ratMomentPoly, momentPoly]

theorem ratCumulativeMass_cast (t : ℚ) : (ratCumulativeMass t : ℝ) = cumulativeMass t := by
  have hl : t ≤ -1 ↔ (t : ℝ) ≤ -1 := by norm_cast
  have hr : t ≤ 1 ↔ (t : ℝ) ≤ 1 := by norm_cast
  by_cases hleft : t ≤ -1
  · simp [ratCumulativeMass, cumulativeMass, hleft, hl.mp hleft]
  by_cases hright : t ≤ 1
  · simp [ratCumulativeMass, cumulativeMass, hleft, hright, not_congr hl |>.mp hleft,
      hr.mp hright, ratMassPoly_cast]
  · simp [ratCumulativeMass, cumulativeMass, hleft, hright, not_congr hl |>.mp hleft,
      not_congr hr |>.mp hright]

theorem ratPrimitive_cast (t : ℚ) : (ratPrimitive t : ℝ) = primitive t := by
  have hl : t ≤ -1 ↔ (t : ℝ) ≤ -1 := by norm_cast
  have hr : t ≤ 1 ↔ (t : ℝ) ≤ 1 := by norm_cast
  by_cases hleft : t ≤ -1
  · simp [ratPrimitive, primitive, hleft, hl.mp hleft]
  by_cases hright : t ≤ 1
  · simp [ratPrimitive, primitive, hleft, hright, not_congr hl |>.mp hleft,
      hr.mp hright, primitivePoly, ratMassPoly_cast, ratMomentPoly_cast]
  · simp [ratPrimitive, primitive, hleft, hright, not_congr hl |>.mp hleft,
      not_congr hr |>.mp hright]

theorem ratScaledPrimitive_cast (a v : ℚ) :
    (ratScaledPrimitive a v : ℝ) = scaledPrimitive a v := by
  simp only [ratScaledPrimitive, Rat.cast_mul, Rat.cast_pow, ratPrimitive_cast,
    Rat.cast_div, Rat.cast_sub, scaledPrimitive]

theorem ratScaledMass_cast (a v : ℚ) :
    (ratScaledMass a v : ℝ) = scaledMass a v := by
  simp only [ratScaledMass, Rat.cast_mul, Rat.cast_pow, ratCumulativeMass_cast,
    Rat.cast_div, Rat.cast_sub, scaledMass]

theorem exists_rat_oracle_index (v : ℚ) (hv : 0 < v) : ∃ N, 2*ratScale N < v := by
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  obtain ⟨N, hN⟩ := exists_scale_lt (half_pos hvr)
  refine ⟨N, ?_⟩
  have ht : (2 : ℝ)*(ratScale N : ℝ) < (v : ℝ) := by rw [ratScale_cast]; linarith
  exact_mod_cast ht

def rationalOracleIndex (v : ℚ) (hv : 0 < v) : ℕ := Nat.find (exists_rat_oracle_index v hv)

def rationalValueOracle (v : ℚ) : ℚ := if hv : 0 < v then
  let N := rationalOracleIndex v hv
  (∑ j ∈ Finset.range N, ratScaledPrimitive (ratScale j) v) +
    ((64/45 : ℚ)*(ratScale N)^2)*v - (128/105 : ℚ)*(ratScale N)^3
  else 0

def rationalDerivativeOracle (v : ℚ) : ℚ := if hv : 0 < v then
  let N := rationalOracleIndex v hv
  (∑ j ∈ Finset.range N, ratScaledMass (ratScale j) v) + (64/45 : ℚ)*(ratScale N)^2
  else 0

theorem rationalOracleIndex_tail_bound (v : ℚ) (hv : 0 < v) (j : ℕ)
    (hj : rationalOracleIndex v hv ≤ j) : scale j+(scale j)^5 < (v : ℝ) := by
  have hN := Nat.find_spec (exists_rat_oracle_index v hv)
  have ht : (2 : ℝ)*scale (rationalOracleIndex v hv) < v := by
    rw [← ratScale_cast]
    exact_mod_cast hN
  have hj' := scale_antitone hj
  linarith [scale_width_le_half j, scale_pos j]

theorem rationalValueOracle_correct (v : ℚ) : (rationalValueOracle v : ℝ) = sourcePrimitive v := by
  by_cases hv : 0 < v
  · rw [rationalValueOracle, dif_pos hv]
    dsimp only
    rw [← seriesPrimitive_eq_source,
      seriesPrimitive_tail_formula (rationalOracleIndex v hv) v (rationalOracleIndex_tail_bound v hv),
      tailMass_eq, tailMoment_eq]
    simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat, ratScaledPrimitive_cast, ratScale_cast]
  · rw [rationalValueOracle, dif_neg hv, Rat.cast_zero, ← seriesPrimitive_eq_source]
    symm
    apply seriesPrimitive_nonpos
    exact_mod_cast le_of_not_gt hv

theorem rationalDerivativeOracle_correct (v : ℚ) :
    (rationalDerivativeOracle v : ℝ) = deriv sourcePrimitive v := by
  by_cases hv : 0 < v
  · rw [rationalDerivativeOracle, dif_pos hv]
    dsimp only
    rw [(sourcePrimitive_hasDerivAt v).deriv,
      seriesMass_tail_formula (rationalOracleIndex v hv) v (rationalOracleIndex_tail_bound v hv), tailMass_eq]
    simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat, ratScaledMass_cast, ratScale_cast]
  · rw [rationalDerivativeOracle, dif_neg hv, Rat.cast_zero, (sourcePrimitive_hasDerivAt v).deriv]
    symm
    apply seriesMass_nonpos
    exact_mod_cast le_of_not_gt hv

def ratBump (t : ℚ) : ℚ := if |t| ≤ 1 then (1-t^2)^2 else 0
def ratScaledDensity (a v : ℚ) : ℚ := (a^3)⁻¹ * ratBump ((v-a)/a^5)
def rationalSecondDerivativeOracle (v : ℚ) : ℚ := if hv : 0 < v then
  let N := rationalOracleIndex v hv
  ∑ j ∈ Finset.range N, ratScaledDensity (ratScale j) v
  else 0

theorem ratBump_cast (t : ℚ) : (ratBump t : ℝ) = bump t := by
  have h : |t| ≤ 1 ↔ |(t : ℝ)| ≤ 1 := by norm_cast
  rw [bump_eq_source]
  by_cases ht : |t| ≤ 1
  · simp [ratBump, ht, h.mp ht]
  · simp [ratBump, ht, not_congr h |>.mp ht]

theorem ratScaledDensity_cast (a v : ℚ) : (ratScaledDensity a v : ℝ) = scaledDensity a v := by
  simp only [ratScaledDensity, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, ratBump_cast,
    Rat.cast_div, Rat.cast_sub, scaledDensity]

theorem sourcePrimitive_second_derivative_pos {v : ℝ} (hv : 0 < v) :
    deriv (deriv sourcePrimitive) v = density v := by
  have he : deriv sourcePrimitive = seriesMass := funext fun t => (sourcePrimitive_hasDerivAt t).deriv
  rw [he]
  exact (seriesMass_hasDerivAt_pos hv).deriv

theorem sourcePrimitive_second_derivative_nonpos {v : ℝ} (hv : v ≤ 0) :
    deriv (deriv sourcePrimitive) v = 0 := by
  rcases hv.eq_or_lt with he | hv
  · rw [he]
    exact sourcePrimitive_second_derivative_zero
  have he : deriv sourcePrimitive = seriesMass := funext fun t => (sourcePrimitive_hasDerivAt t).deriv
  rw [he]
  have hd : HasDerivAt seriesMass 0 v := by
    apply (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hv] with t ht
    exact seriesMass_nonpos ht.le
  exact hd.deriv

theorem rationalSecondDerivativeOracle_correct (v : ℚ) :
    (rationalSecondDerivativeOracle v : ℝ) = deriv (deriv sourcePrimitive) v := by
  by_cases hv : 0 < v
  · rw [rationalSecondDerivativeOracle, dif_pos hv]
    dsimp only
    rw [sourcePrimitive_second_derivative_pos (by exact_mod_cast hv),
      density_tail_formula (rationalOracleIndex v hv) v (rationalOracleIndex_tail_bound v hv)]
    simp only [Rat.cast_sum, ratScaledDensity_cast, ratScale_cast]
  · rw [rationalSecondDerivativeOracle, dif_neg hv, Rat.cast_zero,
      sourcePrimitive_second_derivative_nonpos (by exact_mod_cast le_of_not_gt hv)]

theorem scale_eq_source (N : ℕ) : scale N = (2 : ℝ)^(-((N+2 : ℕ) : ℤ)) := by
  rw [zpow_neg, zpow_natCast]
  simp only [scale, one_div, inv_pow]

def RationalSpikeOracleTarget : Prop :=
  ∀ v : ℚ, (rationalValueOracle v : ℝ) = sourcePrimitive v ∧
    (rationalDerivativeOracle v : ℝ) = deriv sourcePrimitive v ∧
    (rationalSecondDerivativeOracle v : ℝ) = deriv (deriv sourcePrimitive) v

theorem rationalSpikeOracle : RationalSpikeOracleTarget := fun v =>
  ⟨rationalValueOracle_correct v, rationalDerivativeOracle_correct v, rationalSecondDerivativeOracle_correct v⟩

end BfgsVerification.NormalSpike
