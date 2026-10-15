import BfgsVerification.EReconstructionFacts
import BfgsVerification.RidgeConvergence
import BfgsVerification.UnexcitedMetric
import BfgsArticle.AdmissibleRunExistence
import BfgsArticle.Coverage.Companion.Ch11U

/-!
# Lean coverage: `companion/chapters/14_E.tex`

Chapter 14 of the companion ("Formal correspondence and the evidence boundary", label `comp:E`).
Register: `editorial/lean_coverage/register/C_14_E.json`. The chapter is generated from the frozen
source `bfgs_lean_stage1/master_report/latex/chapters/verification.tex` (spans
`E.span.1`-`E.span.26`) by `editorial/generate_companion.py`, which adds the introduction (line 3)
and the dated verification record `companion/current_verification.tex` (line 5; register
`C_current_verification.json`, module `CurrentVerification`).

## Reading of the chapter

* Most sentences describe software, builds, audits, files and commands: they are `NON_CLAIM`, and
  every count, path, script and option they name was checked (notes in the register).
* The mathematical sentences say what the reconstructed Lean suites prove (Section 14.3), which
  results have proof chains and which questions stay open (Section 14.4). They restate chapter
  results and are `SAME_AS` the chapter items (never a `DISCREPANCY` item: for example the
  companion's Theorem `L:thm:local` is replaced by the article's Theorem `art:local-failure-lower`
  and by `C/13_L/prose/078`, and `C/05_G/prose/063` by `prose/065`, `prose/068`). Four sentences
  have no chapter item that states them exactly; this module states them:
  - D-symbolic (line 64): the generic update identities, `update_identities`;
  - V-ridges (line 152): the scalar-ridge objective satisfies the hypotheses of the planar
    convergence theorem, hence every run converges, `scalar_ridge_implication`;
  - C-planar-numerical (line 184) and U-multidimensional-numerical (line 192): convergence implies
    that every positive tolerance on the objective value is eventually attained,
    `planar_tolerance`, `spike_tolerance`.
* Line 210, "The broader questions explicitly marked open in Chapters 8 and 7 are not proved", is
  `OPEN` with the chapter groups' propositions `Ch08A.GeneralDimensionalConjecture`,
  `Ch07H.ZeroValueIterateQuestion` and `Ch07H.TiltNoInfiniteRunQuestion` (still open).
* Imports: as rule 6 of `editorial/lean_coverage/README.md` allows for the wave-3 modules, this
  module imports the finished chapter module `Ch11U`, for the spike objective (11.20)
  (`spike_objective_convergence`, `spike_run2`, `spike_objective_def2`).

## Corrected discrepancies (15 October 2026, see the register)

* Line 18 (`C/14_E/prose/013`), "The stable-manifold conclusion in L follows ...", and line 136
  (`C/14_E/prose/061`), "The explicit four-piece objective in R is ...": the source letters of
  Chapters 13 and 4 were printed reference labels that resolve to nothing in the companion (typo,
  as `C/09_C/prose/117`); since the correction M29 they read `Chapter~\ref{comp:L}` and
  `Chapter~\ref{comp:R}`. The mathematics of both sentences is proved
  (`LowerCurvature.stable_manifold_positive_scale`, `Ch13L.global_failure`;
  `Ch04R.fourPiece_failure_run`).

## Wording points (applied on 15 October 2026; see the register notes)

* Line 184 (W27): the basin was implicit ("the stated planar example converges": proved from its
  basin $F(x_0)<1/100$; a second, falsely affine-critical triple point near $(3.51,2.65)$, found
  numerically, blocks the planar corollary on high sublevels), and "every positive displayed
  tolerance" referred to nothing (no tolerance is displayed; the source report measured
  $F<10^{-45}$); the sentence now reads "converges from its basin~\eqref{C:eq:explicitbasin}, and
  hence every positive tolerance on its objective value is eventually attained". Line 192: "the
  printed positive tolerance" ($F<10^{-28}$) now reads "every positive tolerance".
* Line 112 (W28): the M-mixed summary now starts "Along runs with bounded gradients"; every result
  it names uses a uniform gradient bound (as W1).
* Line 48 (W29): the suite labels of Section 14.3 are the original report's suite names, whose
  letters are not chapter letters, as the sentence now says.
* Software sentences (W30): line 226 now says that the README describes the read-only check and
  that the runner prints the new timestamped output directory; line 16, "each retained assertion
  here has a reviewed formal correspondence", holds again after the corrections and is unchanged.

## Items

| Item | Line | Lean |
|---|---|---|
| `prose/034` | 64 | `update_identities` |
| `prose/067` | 152 | `scalar_ridge_implication` |
| `prose/076` | 184 | `planar_tolerance` |
| `prose/079` | 192 | `spike_tolerance` |

Three `example`s at the end show that the hypotheses of `scalar_ridge_implication`,
`planar_tolerance` and `spike_tolerance` hold for some objective with an admissible run, and one
that those of `update_identities` can hold.
-/

noncomputable section
open scoped Topology
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch14E

/-! ### D-symbolic (line 64) -/

/-- Item `C/14_E/prose/034` (`companion/chapters/14_E.tex:64`): "The inverse and Hessian updates,
their secant identities, determinant and positivity properties [...] are Lean equalities or
inequalities." For $H\succ0$ and $t=y^Ts>0$, the inverse update
$H_+=(I-sy^T/t)H(I-ys^T/t)+ss^T/t$ (the library's `inverseBFGS`) and $B=H^{-1}$:
the Hessian update $B_+=H_+^{-1}=B-Bss^TB/(s^TBs)+yy^T/t$, the secant identities $H_+y=s$ and
$B_+s=y$, the determinant identity $\det H_+=(s^TBs/t)\det H$, and positivity $H_+\succ0$,
$B_+\succ0$. -/
theorem update_identities {n : ℕ} (H : Mat n) (hH : H.PosDef) (s y : Vec n)
    (ht : 0 < dot y s) (Hplus : Mat n)
    (hHplus : Hplus = (1 - (dot y s)⁻¹ • outer s y) * H * (1 - (dot y s)⁻¹ • outer y s) +
      (dot y s)⁻¹ • outer s s) :
    Hplus⁻¹ = H⁻¹ - (dot s (H⁻¹ *ᵥ s))⁻¹ • outer (H⁻¹ *ᵥ s) (H⁻¹ *ᵥ s) +
        (dot y s)⁻¹ • outer y y ∧
      Hplus *ᵥ y = s ∧ Hplus⁻¹ *ᵥ s = y ∧
      Hplus.det = dot s (H⁻¹ *ᵥ s) / dot y s * H.det ∧
      Hplus.PosDef ∧ Hplus⁻¹.PosDef := by
  have hdef : Hplus = inverseBFGS H s y := hHplus
  rw [hdef]
  have hs : s ≠ 0 := by
    rintro rfl
    simp [dot] at ht
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  -- The general Hessian update is the library's run form with $g=-Bs$ and $\alpha=1$.
  set g : Vec n := -(H⁻¹ *ᵥ s) with hg
  have hHg : H *ᵥ g = -s := by
    rw [hg, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hstep : bfgsStep H g 1 = s := by
    simp [bfgsStep, hHg]
  have hg0 : g ≠ 0 := by
    intro h0
    apply hs
    have h := hHg
    rw [h0, Matrix.mulVec_zero] at h
    exact neg_eq_zero.mp h.symm
  have hE : metricEnergy H g = dot s (H⁻¹ *ᵥ s) := by
    rw [metricEnergy, hHg, hg]
    simp [dot, Finset.sum_neg_distrib, mul_comm]
  have hO : outer g g = outer (H⁻¹ *ᵥ s) (H⁻¹ *ᵥ s) := by
    funext i j
    simp [outer, hg]
  have hU := hessianUpdate hH hg0 y one_pos (by rw [hstep]; exact ht)
  rw [hstep, hE, hO] at hU
  have hpd := inverseBFGS_posDef hH s y ht
  exact ⟨hU, EReconstruction.inverse_update_secant H s y ht.ne',
    EReconstruction.hessian_update_secant hH s y ht, inverseBFGS_det hH s y ht.ne', hpd,
    hpd.inv⟩

/-! ### V-ridges (line 152) -/

/-- Item `C/14_E/prose/067` (`companion/chapters/14_E.tex:152`): "the scalar-ridge implication
into the planar convergence theorem [is an] operative formal result". The scalar-ridge objective
$F(u,v)=\max\{a(u)+pv,\ b(u)-qv\}$, with $a,b$ convex and $C^2$, $p,q>0$, the profile
$\varphi=(qa+pb)/(p+q)$ uniquely minimized at $u$, and $a'',b''>0$ away from $u$ (the hypotheses of
the original headline), satisfies every hypothesis of the planar convergence theorem (Corollary
`art:planar-convergence` of the article, Corollary `C:cor:AC`, in the setting of `C:thm:cluster`):
$F$ is convex and all its sublevels are compact; $x_*=(u,(b(u)-a(u))/(p+q))$ is the unique
minimizer, with value $\varphi(u)$; no level set has a nontrivial boundary segment; at every
non-affine-critical point $F$ is $C^2$ or a regular convex two-branch maximum; there is no false
affine criticality. Hence every infinite admissible run converges: $F(x_k)\to F(x_*)$ and
$x_k\to x_*$. -/
theorem scalar_ridge_implication {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : ConvexOn ℝ univ a) (hcb : ConvexOn ℝ univ b) {p q u : ℝ} (hp : 0 < p) (hq : 0 < q)
    (φ : ℝ → ℝ) (hφ : ∀ t, φ t = (q * a t + p * b t) / (p + q))
    (hmin : ∀ t, φ u ≤ φ t) (hunique : ∀ t, φ t = φ u → t = u)
    (ha'' : ∀ t, t ≠ u → 0 < deriv (deriv a) t) (hb'' : ∀ t, t ≠ u → 0 < deriv (deriv b) t)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (a (x 0) + p * x 1) (b (x 0) - q * x 1))
    (xstar : Vec 2) (hxstar : xstar = ![u, (b u - a u) / (p + q)]) :
    (ConvexOn ℝ univ F ∧ ∀ c : ℝ, IsCompact {x | F x ≤ c}) ∧
      ((∀ z, F xstar ≤ F z) ∧ (∀ z, F z = F xstar → z = xstar) ∧ F xstar = φ u) ∧
      (∀ (ℓ : ℝ) (x y : Vec 2), segment ℝ x y ⊆ frontier {w | F w ≤ ℓ} → x = y) ∧
      (∀ x, ¬AffineCriticalObjective.IsAffineCritical F x →
        ContDiffAt ℝ 2 F x ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F x) ∧
      (∀ x, AffineCriticalObjective.AffineCorrectAt F x) ∧
      ∀ R : AdmissibleBFGSRun 2 F,
        Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) := by
  have hFe : F = RidgeSupersession.objective a b p q := funext hF
  have hφe : φ = RidgeSupersession.profile a b p q := funext hφ
  have hxe : xstar = RidgeSupersession.optimizer a b p q u := hxstar
  subst hFe hφe hxe
  have hval := RidgeSupersession.objective_optimizer (a := a) (b := b) (add_pos hp hq).ne' u
  have hconv := RidgeSupersession.objective_convex hca hcb p q
  have hm := RidgeSupersession.optimizer_minimum hp hq hmin
  have hu := RidgeSupersession.optimizer_unique hp hq hmin hunique
  refine ⟨⟨hconv, fun c => Localization.sublevel_compact hconv _ hm hu c⟩,
    ⟨hm, fun z hz => hu z hz, hval⟩,
    fun ℓ x y hseg => RidgeSupersession.strict_contours
      (RidgeSupersession.strictConvex_of_second_pos_except ha u ha'')
      (RidgeSupersession.strictConvex_of_second_pos_except hb u hb'') hp hq ℓ x y hseg,
    fun x hn => RidgeSupersession.source_regular ha hb hca hcb hp hq x hn,
    fun x => RidgeSupersession.source_affineCorrect ha hb hca hcb hp hq hmin hunique x,
    fun R => ?_⟩
  rw [hval]
  exact RidgeSupersession.fullBFGS_convergence ha hb hca hcb hp hq hmin hunique ha'' hb'' R

/-! ### The numerical suites (lines 184 and 192) -/

/-- Item `C/14_E/prose/076` (`companion/chapters/14_E.tex:184`): "The operative statement is
analytic: the stated planar example converges from its basin~\eqref{C:eq:explicitbasin}, and hence
every positive tolerance on its objective value is eventually attained." (Wording point W27
applied on 15 October 2026; before "the stated planar example converges, and hence every positive
displayed tolerance is eventually attained".) The planar example is the explicit three-quadratic
example of Section 9.8, $F=\max\{u+u^2+v^2/2,\ v+u^2/2+3v^2/2,\ -u-v+3u^2/2+v^2\}$, with its basin
$F(x_0)<1/100$ (`C:eq:explicitbasin`): every
infinite admissible run from the basin has $F(x_k)\to0$ (the minimum value) and $x_k\to0$, and
hence for every tolerance $\varepsilon>0$ (on the objective value, as the source suite's
$F<10^{-45}$) eventually $F(x_k)<\varepsilon$. -/
theorem planar_tolerance (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x)))
    (R : AdmissibleBFGSRun 2 F) (h0 : F (R.x 0) < 1 / 100) :
    (Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ k ≥ N, F (R.x k) < ε := by
  obtain ⟨-, rfl⟩ := PlanarQuadraticExample.eq_branch_objective f hf F hF
  have hc := PlanarQuadraticExample.fullBFGS_explicit_basin R h0
  exact ⟨hc, fun ε hε => EReconstruction.eventually_below_tolerance _ hc.1 hε⟩

/-- Item `C/14_E/prose/079` (`companion/chapters/14_E.tex:192`): "Its convergence implies
eventual attainment of every positive tolerance." (Wording point W27 applied on 15 October 2026;
before "the printed positive tolerance".) For the fixed-normal spike objective
(11.20), $F(u,v)=\tfrac12\|u\|^2+\tfrac12v^2+|v|+r(v)$ on $\mathbb R^{m+2}$ (points $(v,u)$, every
allowed dimension $n=m+2\ge2$), every infinite admissible run has $F(x_k)\to0$ (the minimum value)
and $x_k\to0$, and hence for every tolerance $\varepsilon>0$ (on the objective value, as the source
suite's $F<10^{-28}$) eventually $F(x_k)<\varepsilon$. -/
theorem spike_tolerance (m : ℕ) (F : Vec (m + 2) → ℝ)
    (hF_def : ∀ (u : Vec (m + 1)) (v : ℝ),
      F (Fin.cons v u) = (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v)
    (R : AdmissibleBFGSRun (m + 2) F) :
    (Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ k ≥ N, F (R.x k) < ε := by
  have hc := BfgsCoverage.Companion.Ch11U.spike_objective_convergence m F hF_def R
  exact ⟨hc, fun ε hε => EReconstruction.eventually_below_tolerance _ hc.1 hε⟩

/-! ### Non-vacuity -/

/-- The hypotheses of `update_identities` can hold: $H=I$ and $s=y=e_0$ in $\mathbb R^1$. -/
example : ∃ (H : Mat 1) (s y : Vec 1), H.PosDef ∧ 0 < dot y s :=
  ⟨1, fun _ => 1, fun _ => 1, Matrix.PosDef.one, by simp [dot]⟩

/-- The hypotheses of `scalar_ridge_implication` hold for $a(t)=b(t)=t^2$, $p=q=1$, $u=0$, where
$F(u,v)=\max\{u^2+v,u^2-v\}=u^2+|v|$ is the mixed benchmark, and an admissible run on it exists
(`UnexcitedMetric.run`). -/
example : ∃ (a b φ : ℝ → ℝ) (p q u : ℝ) (F : Vec 2 → ℝ),
    ContDiff ℝ 2 a ∧ ContDiff ℝ 2 b ∧ ConvexOn ℝ univ a ∧ ConvexOn ℝ univ b ∧ 0 < p ∧ 0 < q ∧
      (∀ t, φ t = (q * a t + p * b t) / (p + q)) ∧ (∀ t, φ u ≤ φ t) ∧
      (∀ t, φ t = φ u → t = u) ∧ (∀ t, t ≠ u → 0 < deriv (deriv a) t) ∧
      (∀ t, t ≠ u → 0 < deriv (deriv b) t) ∧
      (∀ x, F x = max (a (x 0) + p * x 1) (b (x 0) - q * x 1)) ∧
      Nonempty (AdmissibleBFGSRun 2 F) := by
  have hd : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    simp
  have hdd : ∀ t : ℝ, deriv (deriv (fun t : ℝ => t ^ 2)) t = 2 := by
    intro t
    rw [hd]
    have h : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    exact h.deriv
  refine ⟨fun t => t ^ 2, fun t => t ^ 2, fun t => (1 * t ^ 2 + 1 * t ^ 2) / (1 + 1), 1, 1, 0,
    UnexcitedMetric.objective, by fun_prop, by fun_prop, Even.convexOn_pow (by norm_num),
    Even.convexOn_pow (by norm_num), one_pos, one_pos, fun t => rfl, fun t => ?_, fun t ht => ?_,
    fun t _ => by rw [hdd]; norm_num, fun t _ => by rw [hdd]; norm_num, fun x => ?_,
    ⟨UnexcitedMetric.run 1 1 (1 / 2) (1 / 4) (1 / 2) one_pos one_pos (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)⟩⟩
  · show (1 * (0 : ℝ) ^ 2 + 1 * (0 : ℝ) ^ 2) / (1 + 1) ≤ (1 * t ^ 2 + 1 * t ^ 2) / (1 + 1)
    have := sq_nonneg t
    norm_num
    positivity
  · change (1 * t ^ 2 + 1 * t ^ 2) / (1 + 1) = (1 * (0 : ℝ) ^ 2 + 1 * (0 : ℝ) ^ 2) / (1 + 1) at ht
    have h2 : t ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  · simp only [UnexcitedMetric.objective, one_mul]
    rcases le_total 0 (x 1) with h | h
    · rw [abs_of_nonneg h, max_eq_left (by linarith)]
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]
      ring

/-- The hypotheses of `planar_tolerance` hold: the three-quadratic objective has an admissible run
with $F(x_0)<1/100$ (`PlanarQuadraticExample.nonradial_example_nonvacuous`, $H_0=I$,
$c_1=1/4$, $c_2=1/2$). -/
example : ∃ (f : Fin 3 → Vec 2 → ℝ) (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F),
    (∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧
      f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2) ∧
    (∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) ∧ F (R.x 0) < 1 / 100 := by
  have hf : ∀ x : Vec 2, PlanarQuadraticExample.branch 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      PlanarQuadraticExample.branch 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧
      PlanarQuadraticExample.branch 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2 := by
    intro x
    simp [PlanarQuadraticExample.branch]
  obtain ⟨R, -, -, -, h0, -⟩ := PlanarQuadraticExample.nonradial_example_nonvacuous
    PlanarQuadraticExample.branch hf PlanarQuadraticExample.objective (fun x => rfl) 1
    Matrix.PosDef.one (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, _, R, hf, fun x => rfl, h0⟩

/-- The hypotheses of `spike_tolerance` hold: the spike objective (11.20) in dimension $2$
(`m = 0`) has an admissible run (`Ch11U.spike_run2`, from $x_0=e_v$ with $H_0=I$). -/
example : ∃ (F : Vec 2 → ℝ), (∀ (u : Vec 1) (v : ℝ),
      F (Fin.cons v u) =
        (1 / 2) * sqNorm u + (1 / 2) * v ^ 2 + |v| + NormalSpike.sourcePrimitive v) ∧
    Nonempty (AdmissibleBFGSRun 2 F) := by
  obtain ⟨R, -⟩ := BfgsCoverage.Companion.Ch11U.spike_run2
  exact ⟨_, BfgsCoverage.Companion.Ch11U.spike_objective_def2, ⟨R⟩⟩

end BfgsCoverage.Companion.Ch14E
