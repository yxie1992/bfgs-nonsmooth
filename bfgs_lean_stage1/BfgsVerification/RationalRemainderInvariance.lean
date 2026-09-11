import BfgsVerification.RationalLocalReciprocity

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem polynomial_eventually_ne_punctured {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    ∀ᶠ x in 𝓝[≠] a, p.eval x ≠ 0 := by
  have h := (rootFactor p a).continuousAt.eventually_ne (rootFactor_eval_ne_zero hp a)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxa
  rw [rootFactor_eval_factorization p a x]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hxa)) hx

theorem tendsto_add_finite_atTop_iff {f g : ℝ → ℝ} {l : Filter ℝ} {b : ℝ}
    (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x => f x + g x) l atTop ↔ Tendsto f l atTop := by
  constructor
  · intro h
    simpa using h.atTop_add hg.neg
  · exact fun h => h.atTop_add hg

theorem tendsto_add_finite_atBot_iff {f g : ℝ → ℝ} {l : Filter ℝ} {b : ℝ}
    (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x => f x + g x) l atBot ↔ Tendsto f l atBot := by
  constructor
  · intro h
    simpa using h.atBot_add hg.neg
  · exact fun h => h.atBot_add hg

theorem localCauchyIndex_eventuallyEq {f g : ℝ → ℝ} {a : ℝ}
    (h : f =ᶠ[𝓝[≠] a] g) : localCauchyIndex f a = localCauchyIndex g a := by
  classical
  have hl : f =ᶠ[𝓝[<] a] g := h.filter_mono (nhdsWithin_mono a (by intro x hx; exact ne_of_lt hx))
  have hr : f =ᶠ[𝓝[>] a] g := h.filter_mono (nhdsWithin_mono a (by intro x hx; exact ne_of_gt hx))
  have hlt (l : Filter ℝ) := tendsto_congr' (l₂ := l) hl
  have hrt (l : Filter ℝ) := tendsto_congr' (l₂ := l) hr
  have h1 := and_congr (hlt atBot) (hrt atTop)
  have h2 := and_congr (hlt atTop) (hrt atBot)
  exact if_congr h1 rfl (if_congr h2 rfl rfl)

theorem localCauchyIndex_add_of_continuousAt (f g : ℝ → ℝ) (a : ℝ)
    (hg : ContinuousAt g a) :
    localCauchyIndex (fun x => f x + g x) a = localCauchyIndex f a := by
  classical
  have hl := hg.tendsto.mono_left (show 𝓝[<] a ≤ 𝓝 a from nhdsWithin_le_nhds)
  have hr := hg.tendsto.mono_left (show 𝓝[>] a ≤ 𝓝 a from nhdsWithin_le_nhds)
  have h1 := and_congr (tendsto_add_finite_atBot_iff (f := f) hl)
    (tendsto_add_finite_atTop_iff (f := f) hr)
  have h2 := and_congr (tendsto_add_finite_atTop_iff (f := f) hl)
    (tendsto_add_finite_atBot_iff (f := f) hr)
  exact if_congr h1 rfl (if_congr h2 rfl rfl)

theorem localCauchyIndex_polynomial_add_mul (p r : Polynomial ℝ) {q : Polynomial ℝ}
    (hq : q ≠ 0) (a : ℝ) :
    localCauchyIndex (fun x => (p+q*r).eval x / q.eval x) a =
      localCauchyIndex (fun x => p.eval x / q.eval x) a := by
  calc
    _ = localCauchyIndex (fun x => p.eval x / q.eval x + r.eval x) a := by
      apply localCauchyIndex_eventuallyEq
      filter_upwards [polynomial_eventually_ne_punctured hq a] with x hx
      simp only [eval_add, eval_mul]
      field_simp
      ring
    _ = _ := localCauchyIndex_add_of_continuousAt _ _ _ r.continuousAt

theorem rationalCauchyIndex_add_mul (p r : Polynomial ℝ) {q : Polynomial ℝ}
    (hq : q ≠ 0) : rationalCauchyIndex (p+q*r) q = rationalCauchyIndex p q := by
  classical
  unfold rationalCauchyIndex
  apply Finset.sum_congr rfl
  intro a _
  exact localCauchyIndex_polynomial_add_mul p r hq a

theorem rationalCauchyIndex_mod (p : Polynomial ℝ) {q : Polynomial ℝ} (hq : q ≠ 0) :
    rationalCauchyIndex p q = rationalCauchyIndex (p % q) q := by
  have he : p % q + q*(p/q) = p := EuclideanDomain.mod_add_div p q
  calc
    _ = rationalCauchyIndex (p % q + q*(p/q)) q := by rw [he]
    _ = _ := rationalCauchyIndex_add_mul _ _ hq

end RealAlgebraicGeometry
end BfgsVerification
