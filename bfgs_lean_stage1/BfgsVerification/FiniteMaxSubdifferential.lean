import BfgsVerification.ConvexSubdifferential
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! Exact subdifferentials of locally represented finite differentiable maxima.
The branches need not be convex. Only the full finite objective is convex. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace BfgsVerification
namespace ConvexSubdifferential

/-- A differentiable lower contact supports the full convex objective globally. -/
theorem supports_of_local_minorant {n : ℕ} {F f : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x g : Vec n}
    (hg : HasFDerivAt f (gradientFunctional g) x) (heq : f x = F x)
    (hminor : ∀ᶠ z in 𝓝 x, f z ≤ F z) : Homogeneous.Supports F x g := by
  intro z
  let p : ℝ → Vec n := fun t => t • (z - x) + x
  have hp : HasDerivAt p (z - x) 0 := by
    simpa only [p, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (z - x)).add_const x
  have hd : HasDerivAt (f ∘ p) (dot g (z - x)) 0 := by
    simpa using hg.comp_hasDerivAt_of_eq 0 hp (by simp [p])
  have hlim : Tendsto (fun t => (f (p t) - F x) / t) (𝓝[>] (0 : ℝ))
      (𝓝 (dot g (z - x))) := by
    simpa [div_eq_mul_inv, mul_comm, heq, p] using hd.tendsto_slope_zero_right
  have hmp : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (p t) ≤ F (p t) :=
    (hp.continuousAt.tendsto.eventually (by simpa [p] using hminor)).filter_mono
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [hmp, hsmall, self_mem_nhdsWithin] with t hft ht1 ht0
  have ht : 0 < t := ht0
  have hc := hF.2 (mem_univ x) (mem_univ z) (by linarith : 0 ≤ 1 - t)
    ht.le (by ring : (1 - t) + t = 1)
  have hpoint : (1 - t) • x + t • z = p t := by dsimp [p]; module
  rw [hpoint] at hc
  simp only [smul_eq_mul] at hc
  apply (div_le_iff₀ ht).2
  nlinarith

/-- An exact local finite-maximum representation, including attainment. -/
def LocalFiniteMax {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (x : Vec n) : Prop :=
  ∀ᶠ z in 𝓝 x, IsGreatest (Set.range (fun i => f i z)) (F z)

/-- The original active indices, retaining coincident branch gradients. -/
def activeIndices {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (x : Vec n) : Finset (Fin m) :=
  Finset.univ.filter (fun i => f i x = F x)

@[simp] theorem mem_activeIndices {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {x : Vec n} {i : Fin m} :
    i ∈ activeIndices F f x ↔ f i x = F x := by simp [activeIndices]

theorem activeIndices_nonempty {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {x : Vec n} (hrep : LocalFiniteMax F f x) :
    (activeIndices F f x).Nonempty := by
  obtain ⟨i, hi⟩ := (mem_of_mem_nhds hrep).1
  exact ⟨i, mem_activeIndices.mpr hi⟩

theorem active_gradient_supports {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n}
    {x : Vec n} (hrep : LocalFiniteMax F f x)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x)
    {i : Fin m} (hi : i ∈ activeIndices F f x) :
    g i ∈ subdifferential F x := by
  apply supports_of_local_minorant hF (hg i) (mem_activeIndices.mp hi)
  filter_upwards [hrep] with z hz
  exact hz.2 (mem_range_self i)

/-- A branch with lower value, or with a smaller directional derivative at equal
value, lies strictly below the proposed affine support on a small positive ray. -/
theorem eventually_branch_lt_affine {n : ℕ} {f : Vec n → ℝ} {x g d : Vec n}
    (hg : HasFDerivAt f (gradientFunctional g) x) {v c : ℝ}
    (hv : f x ≤ v) (hc : f x = v → dot g d < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (t • d + x) < v + t * c := by
  have hp : HasDerivAt (fun t : ℝ => t • d + x) d 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).add_const x
  have hd : HasDerivAt (fun t : ℝ => f (t • d + x)) (dot g d) 0 := by
    simpa using hg.comp_hasDerivAt_of_eq 0 hp (by simp)
  rcases hv.eq_or_lt with heq | hlt
  · have hlim : Tendsto (fun t : ℝ => (f (t • d + x) - v) / t)
        (𝓝[>] 0) (𝓝 (dot g d)) := by
      simpa [div_eq_mul_inv, mul_comm, heq] using hd.tendsto_slope_zero_right
    filter_upwards [hlim.eventually_lt_const (hc heq), self_mem_nhdsWithin] with t ht ht0
    have htpos : 0 < t := ht0
    have := (div_lt_iff₀ htpos).mp ht
    linarith
  · have hcst : ContinuousAt (fun t : ℝ => v + t * c) 0 := by fun_prop
    have hev := hd.continuousAt.eventually_lt hcst (by simpa using hlt)
    exact hev.filter_mono nhdsWithin_le_nhds

/-- Exact active-gradient convex-hull formula. All differentiability assumptions
are at the represented point; no branch convexity or C1 neighborhood is needed. -/
theorem subdifferential_eq_active_convexHull {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ} {g : Fin m → Vec n}
    {x : Vec n} (hrep : LocalFiniteMax F f x)
    (hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) x) :
    subdifferential F x = convexHull ℝ (g '' (activeIndices F f x : Set (Fin m))) := by
  classical
  apply subset_antisymm
  · intro a ha
    by_contra hnot
    have hfinite : (g '' (activeIndices F f x : Set (Fin m))).Finite :=
      (activeIndices F f x).finite_toSet.image g
    obtain ⟨l, u, hlu, hua⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) hfinite.isClosed_convexHull hnot
    let d : Vec n := fun i => l (Pi.single i 1)
    have hl (b : Vec n) : l b = dot b d := by
      rw [← gradientFunctional_coordinates l, gradientFunctional_apply]
      exact dotProduct_comm _ _
    have hatx := mem_of_mem_nhds hrep
    have hbranches (i : Fin m) : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        f i (t • d + x) < F x + t * dot a d := by
      apply eventually_branch_lt_affine (hg i) (hatx.2 (mem_range_self i))
      intro hi
      have himem : g i ∈ convexHull ℝ (g '' (activeIndices F f x : Set (Fin m))) :=
        subset_convexHull ℝ _ ⟨i, mem_activeIndices.mpr hi, rfl⟩
      simpa only [hl] using (hlu _ himem).trans hua
    have hp : Tendsto (fun t : ℝ => t • d + x) (𝓝[>] 0) (𝓝 x) := by
      have hcont : Continuous (fun t : ℝ => t • d + x) := by fun_prop
      simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hev := (eventually_all.mpr hbranches).and (hp.eventually hrep)
    obtain ⟨t, hbt, htmax⟩ := hev.exists
    obtain ⟨i, hi⟩ := htmax.1
    have htlt := hbt i
    dsimp only at hi
    rw [hi] at htlt
    have hsupport := ha (t • d + x)
    have hdot : dot a (t • d + x - x) = t * dot a d := by
      rw [add_sub_cancel_right]
      exact dotProduct_smul _ _ _
    rw [hdot] at hsupport
    linarith
  · apply convexHull_min
    · rintro _ ⟨i, hi, rfl⟩
      exact active_gradient_supports hF hrep hg hi
    · exact convex_subdifferential F x

end ConvexSubdifferential
end BfgsVerification
