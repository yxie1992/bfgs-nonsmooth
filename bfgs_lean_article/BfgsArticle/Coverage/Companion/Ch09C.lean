import BfgsArticle.Coverage.Article.Local
import BfgsArticle.Coverage.Article.PlanarGeometry
import BfgsArticle.Coverage.Article.Energy
import BfgsVerification.SpatialQuadraticTargets
import BfgsVerification.ConstantRankTargets
import BfgsVerification.SemialgebraicCriticalGeometry
import BfgsVerification.CriticalSmoothPathValues
import BfgsVerification.ObjectiveSemialgebraicCompositionTargets
import BfgsVerification.AffineSupportPath
import BfgsArticle.AdmissibleRunExistence
import BfgsVerification.LGlobalFailure
import BfgsVerification.BFGSGradientScaling

/-!
# Lean coverage: `companion/chapters/09_C.tex`

Chapter C ("Planar switching and affine-critical cluster points"): Theorem `C:thm:cluster`,
Corollaries `C:cor:AC` and `C:cor:max`, Lemmas `C:lem:steps`, `C:lem:trans`,
`C:lem:transport`, `C:lem:secant`, the displays of their proofs, the construction of the
comparison field (§4, which the chapter gives outside any proof environment), the tame-geometric
alternative (§7.1), the explicit quadratic example (§8) and the higher-dimensional partial
statement and warning (§9), with the prose claims of the chapter. Register:
`editorial/lean_coverage/register/C_09_C.json`.

## Standing assumptions

* §1 (lines 35-53) and the theorem: `F : Vec 2 → ℝ`, `hF : ConvexOn ℝ univ F` ($F$ finite and
  convex), `hFstar : IsLeast (Set.range F) Fstar` ($F$ attains $F_*$), `hb : Fstar < b`,
  `hK : IsCompact {x | F x ≤ b}` ($K=\{F\le b\}$ compact); the two objective-level hypotheses
  `hstrict` (strictly convex positive sublevels, the definition `StrictlyConvexPositiveSublevels`)
  and `hreg` (regular switching away from affine criticality, written as in the TeX, the
  definition `RegularSwitching`); an infinite admissible full-BFGS run `R : AdmissibleBFGSRun 2 F`
  (the article's definition `art:admissible`, which is the chapter's admissibility of lines
  59-69, `Energy.admissible_iff`) starting in $K$ (`hR : R.x 0 ∈ {x | F x ≤ b}`). Statements of
  §§2-3 that do not use the two objective-level hypotheses are stated under the rest
  (line 35); general facts ("a finite convex function has bounded subgradients on a compact set")
  are stated in general.
* §§4-5 (line 162 and the §1 hypotheses at the level $\ell$): a level $F_*<\ell$ whose sublevel is
  strictly convex (`hstrict` at $\ell$), a compact `C ⊆ {x | F x = ℓ}` (not assumed nonempty)
  without affine-critical points (`hnoncrit`) and satisfying the regularity hypothesis at each
  point (`hregular`, TeX form); in §5 valid constants $0<c_1<c_2<1$. A corner $c\in C$ comes with
  its two-branch data (`V`, `f₁`, `f₂`, ...) and its switching curve `p` (display `disp/014`).
* Displays inside proofs are stated under the assumptions of the result and the objects the proof
  has introduced before them (variables with their defining equations). A hypothesis whose name
  starts with `_` is a standing assumption the Lean proof does not use. Where the TeX argues by
  contradiction, the contradiction hypothesis is included only where the statement needs it
  (`contradiction_setup`, `energy_tail_inequality`, and the assumptions of `telescoped_bound`):
  these statements are vacuous by design, since that hypothesis cannot hold together with the
  theorem's (which is what the proof shows); see the docstrings.
* §9: `F : Vec n → ℝ` in any dimension; `ConvexSubdifferential.LocalFiniteMax F f p` is an exact
  finite maximum representation near $p$.

## Notation

* `Vec n = Fin n → ℝ` carries the sup norm; Euclidean quantities are explicit:
  `‖euclideanVector s‖` is $\norm{s}$, `sqNorm s` is $\norm{s}^2$, `dot a b` is $a^Tb$.
* $\mathcal C_{\rm aff}$ is `{p | AffineCriticalObjective.IsAffineCritical F p}`
  (`Local.affineCritical_set_eq`), $\partial F(p)$ is `ConvexSubdifferential.subdifferential F p`,
  \eqref{C:eq:AC} at $p$ is `AffineCorrectAt F p` (`affineCorrectAt_iff`); a cluster point is
  `MapClusterPt p atTop R.x`; $q_k$ = `R.q k`, $d_k=\alpha_kq_k$ = `R.d k`, $s_k=-\alpha_kH_kg_k$.
* An eligible pair (line 247) is `TransportedCertificate.EligiblePair F c₁ c₂ x z g h`
  (`Energy.eligiblePair_iff`); `HomogeneousPlanar.pairDet u v` is $\det(u,v)$ (columns $u,v$).
* $n(\theta)$, $T(\theta)$ are `PlanarTransport.normal`, `tangent`; $h$ and $hn+h_\theta T$ are the
  article's `PlanarGeometry.height` and `PlanarGeometry.fieldFormula`; the constructed field is
  `PlanarObjectiveField.field hF χ v` for smooth ambient cutoffs $\chi_j$ (angular cutoffs
  $\theta\mapsto\chi_j(n(\theta))$) and velocities $v_j$. "Cutoffs" take values in $[0,1]$.
* The example of §8 takes its branches and objective as variables with their defining equations
  (`hf`, `hF`), identified with `PlanarQuadraticExample.branch`, `objective` by `Local.example_eq`.
  The warning of §9 uses `SpatialQuadraticWarning` (`objective`, `Q`, `base`, `step`, `next`,
  `change`, `canonicalField`).

## Items

Each declaration's docstring names its item(s); the register lists the Lean names of every item.
Named results: `cluster`, `cor_AC` and `cor_AC_local`, `cor_max` and `cor_max_hessian`, `steps`,
`transversality`, `transport`, `secant` (with `three_estimates` for their common field). Every
item of the chapter has a final status. The one discrepancy (typo), the stale reference "A's low
affine-critical gap" (line 398, item `C/09_C/prose/117`) for Proposition 8.1
(`A:semialgebraic`), was corrected on 15 October 2026 (M20): the sentence now reads "Combining the
low affine-critical gap of Proposition~\ref{A:semialgebraic} with Theorem~\ref{C:thm:cluster}";
its claim is `semialgebraic_low_basin`. Wording points W8 (lines 93 and 110), W14 (line 151) and
W15 (line 191, "$0\le\chi_j\le1$") were applied on the same day.

## Non-vacuity

The `example`s at the end show that the hypotheses of §1 (with Corollary `C:cor:AC`) hold together
with an actual admissible run starting in $K$ ($u^2+|v|$, `UnexcitedMetric.run`); that the premises
of Lemma `C:lem:steps` hold for an actual run whose values decrease to a level $\ell>F_*$ (a
library failure run on a strongly convex objective); that the standing assumptions of §§4-5 hold
with a nonsmooth point of $C$ (the objective of §8); that the hypotheses of Corollaries
`C:cor:max` (and its Hessian replacement) and `C:cor:AC` (third sentence), the definitions of §8
and the hypotheses of the §7.1 statements hold for the objective of §8, with actual runs started
as close to the minimizer as one likes; that the hypotheses of the §9 partial statement hold, and
that an actual admissible run on the quadratic of §9 exists (`spatialRun`); and that the
assumptions of `telescoping_algebra` hold.
-/

noncomputable section
open scoped Topology NNReal ContDiff
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch09C

/-! ### §1. Statements and assumptions (lines 33-98) -/

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/004` (`companion/chapters/09_C.tex:43`), anchor "Ordinary
stationarity, $0\in\partial F(p)$, implies affine criticality": "Ordinary stationarity,
$0\in\partial F(p)$, implies affine criticality, but not conversely."

For every $F:\R^2\to\R$ and every $p$, $0\in\partial F(p)$ implies $p\in\mathcal C_{\rm aff}$
($0\in\aff\partial F(p)$); and there are a finite convex $F$ (namely $\max\{u,2u\}$,
`Local.affineCritical_not_stationary_example`) and a point $p$ with $p\in\mathcal C_{\rm aff}$
but $0\notin\partial F(p)$. -/
theorem stationary_affineCritical :
    (∀ (F : Vec 2 → ℝ) (p : Vec 2), (0 : Vec 2) ∈ subdifferential F p → IsAffineCritical F p) ∧
      ∃ (F : Vec 2 → ℝ) (p : Vec 2), ConvexOn ℝ univ F ∧ IsAffineCritical F p ∧
        (0 : Vec 2) ∉ subdifferential F p := by
  refine ⟨fun F p h0 => (isAffineCritical_iff_coordinate_affineSpan F p).mpr
    (subset_affineSpan ℝ _ h0), ?_⟩
  obtain ⟨F, hF, hc, hn, -, -⟩ := BfgsCoverage.Article.Local.affineCritical_not_stationary_example
  exact ⟨F, 0, hF, hc, hn⟩

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/004` (`companion/chapters/09_C.tex:43`), "but not conversely", within
the standing assumptions of line 35: $F(u,v)=\max\{u,2u\}+u^2+v^2$ is finite and convex, attains
$F_*=-1/4$ (at $(-1/2,0)$, the only minimizer), its sublevel $K=\{F\le0\}$ ($b=0>F_*$) is
compact, and the point $0\in K$ is affine critical ($(1,0),(2,0)\in\partial F(0)$, whose affine
hull is the $u$-axis) but not stationary ($F(-1/2,0)<F(0)$). -/
theorem affineCritical_not_stationary_standing (F : Vec 2 → ℝ)
    (hFdef : ∀ x, F x = max (x 0) (2 * x 0) + (x 0 ^ 2 + x 1 ^ 2)) :
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) (-1 / 4) ∧ (-1 / 4 : ℝ) < 0 ∧
      IsCompact {x | F x ≤ 0} ∧ F 0 ≤ 0 ∧ IsAffineCritical F 0 ∧
      (0 : Vec 2) ∉ subdifferential F 0 := by
  have hmax : ConvexOn ℝ univ (fun x : Vec 2 => max (x 0) (2 * x 0)) := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply max_le
    · nlinarith [le_max_left (x 0) (2 * x 0), le_max_left (y 0) (2 * y 0)]
    · nlinarith [le_max_right (x 0) (2 * x 0), le_max_right (y 0) (2 * y 0)]
  have hquad : ConvexOn ℝ univ (fun x : Vec 2 => x 0 ^ 2 + x 1 ^ 2) := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain rfl : t = 1 - s := by linarith
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x 0 - y 0)),
      mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x 1 - y 1))]
  have hconv : ConvexOn ℝ univ F := by
    have hfun : F = (fun x : Vec 2 => max (x 0) (2 * x 0)) + fun x : Vec 2 => x 0 ^ 2 + x 1 ^ 2 :=
      funext fun x => hFdef x
    rw [hfun]
    exact hmax.add hquad
  have hlow : ∀ x, (x 0 + 1 / 2) ^ 2 + x 1 ^ 2 - 1 / 4 ≤ F x := fun x => by
    rw [hFdef]
    nlinarith [le_max_left (x 0) (2 * x 0)]
  set xs : Vec 2 := ![-1 / 2, 0] with hxs
  have hFxs : F xs = -1 / 4 := by
    rw [hFdef, hxs]
    norm_num
  have hmin : ∀ x, F xs ≤ F x := fun x => by
    rw [hFxs]
    nlinarith [hlow x, sq_nonneg (x 0 + 1 / 2), sq_nonneg (x 1)]
  have huniq : ∀ x, F x = F xs → x = xs := by
    intro x hx
    rw [hFxs] at hx
    have h := hlow x
    have h0 : x 0 = -1 / 2 := by nlinarith [sq_nonneg (x 0 + 1 / 2), sq_nonneg (x 1)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0 + 1 / 2), sq_nonneg (x 1)]
    ext i
    fin_cases i
    · simpa [hxs] using h0
    · simpa [hxs] using h1
  have hF0 : F 0 = 0 := by
    rw [hFdef]
    simp
  have hsub : ∀ c : ℝ, 1 ≤ c → c ≤ 2 → (![c, 0] : Vec 2) ∈ subdifferential F 0 := by
    intro c hc1 hc2
    rw [mem_subdifferential]
    intro z
    rw [hFdef z, hF0]
    simp only [sub_zero, dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, zero_mul, add_zero]
    rcases le_total 0 (z 0) with h | h
    · nlinarith [le_max_right (z 0) (2 * z 0), mul_le_mul_of_nonneg_right hc2 h,
        sq_nonneg (z 0), sq_nonneg (z 1)]
    · nlinarith [le_max_left (z 0) (2 * z 0), mul_le_mul_of_nonpos_right hc1 h,
        sq_nonneg (z 0), sq_nonneg (z 1)]
  have hcrit : IsAffineCritical F 0 := by
    rw [isAffineCritical_iff_coordinate_affineSpan]
    have h := AffineMap.lineMap_mem (Q := affineSpan ℝ (subdifferential F 0)) (-1 : ℝ)
      (subset_affineSpan ℝ _ (hsub 1 le_rfl (by norm_num)))
      (subset_affineSpan ℝ _ (hsub 2 (by norm_num) le_rfl))
    have he : AffineMap.lineMap (![1, 0] : Vec 2) ![2, 0] (-1 : ℝ) = 0 := by
      ext i
      fin_cases i <;> norm_num [AffineMap.lineMap_apply_module]
    rwa [he] at h
  refine ⟨hconv, ⟨⟨xs, hFxs⟩, by rintro _ ⟨x, rfl⟩; exact hFxs ▸ hmin x⟩, by norm_num,
    Localization.sublevel_compact hconv xs hmin huniq 0, hF0.le, hcrit, fun h0 => ?_⟩
  have h := (mem_subdifferential.mp h0) xs
  rw [hFxs, hF0] at h
  simp [dot] at h
  norm_num at h

/-- Item `C/09_C/prose/005` (`companion/chapters/09_C.tex:47`), anchor "\textbf{Strictly
convex positive sublevels.}": the first objective-level hypothesis, "For every $F_*<t\le b$, the
convex body $K_t=\{F\le t\}$ is strictly convex: its boundary contains no nontrivial line
segment." (Theorem `cluster` writes it out as its hypothesis `hstrict`.) -/
def StrictlyConvexPositiveSublevels (F : Vec 2 → ℝ) (Fstar b : ℝ) : Prop :=
  ∀ t, Fstar < t → t ≤ b → ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y

open AffineCriticalObjective in
/-- Item `C/09_C/prose/009` (`companion/chapters/09_C.tex:49-53`), anchor "\textbf{Regular
switching away from affine criticality.}": the second objective-level hypothesis, including
display `C/09_C/disp/003` (lines 50-52). "At every $p\in K\setminus\mathcal C_{\rm aff}$, either
$F$ is convex $C^2$ on a neighborhood of $p$, or on such a neighborhood $F=\max\{f_1,f_2\}$,
where $f_1,f_2$ are convex $C^2$, both are active at $p$, and $\nabla f_1(p),\nabla f_2(p)$ are
linearly independent." Here $K=\{F\le b\}$; a neighborhood is an open set `V ∋ p`; "convex
$C^2$ on `V`" is `ConvexOn ℝ V f ∧ ContDiffOn ℝ 2 f V` (so `V` is convex in the second
alternative; $F$ is convex everywhere by the standing assumption). (Theorem `cluster` writes it
out as its hypothesis `hreg`.) -/
def RegularSwitching (F : Vec 2 → ℝ) (b : ℝ) : Prop :=
  ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
    (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
    (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
      ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
      (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
      LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])

/-- Item `C/09_C/prose/006` (`companion/chapters/09_C.tex:47`), anchor "the convex body
$K_t=\{F\le t\}$".

Under the standing assumptions of line 35 ($F$ finite and convex, attaining $F_*$, with compact
$K=\{F\le b\}$, $b>F_*$), for every $F_*<t\le b$ the sublevel $K_t=\{F\le t\}$ is a convex
body: convex, compact, with nonempty interior. -/
theorem sublevel_convex_body (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b}) (t : ℝ) (ht : Fstar < t) (htb : t ≤ b) :
    Convex ℝ {x | F x ≤ t} ∧ IsCompact {x | F x ≤ t} ∧ (interior {x | F x ≤ t}).Nonempty := by
  have hcont : Continuous F := convex_continuous hF
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mem_univ, true_and] using hF.convex_le t
  · exact hK.of_isClosed_subset (isClosed_le hcont continuous_const)
      (fun x (hx : F x ≤ t) => (le_trans hx htb : F x ≤ b))
  · obtain ⟨⟨xs, hxs⟩, -⟩ := hFstar
    have hopen : IsOpen {x | F x < t} := isOpen_lt hcont continuous_const
    have hxs' : xs ∈ interior {x | F x < t} := by
      rw [hopen.interior_eq]
      show F xs < t
      rw [hxs]
      exact ht
    exact ⟨xs, interior_mono (fun x (hx : F x < t) => (le_of_lt hx : F x ≤ t)) hxs'⟩

/-- Item `C/09_C/prose/007` (`companion/chapters/09_C.tex:47`), anchor "This is a condition
on the contours, not a uniform lower Hessian bound."

The strict-contour hypothesis does not require a positive lower Hessian bound:
$F(x)=\norm{x}^4$ is convex and $C^2$, has no nontrivial segment in the boundary of any
positive sublevel, and at its minimizer its Hessian has no lower bound $\mu I$, $\mu>0$
(`Local.strict_contours_without_hessian_bound`). -/
theorem contour_condition_not_hessian_bound :
    ∃ F : Vec 2 → ℝ, ConvexOn ℝ univ F ∧ ContDiff ℝ 2 F ∧ (∀ x, F 0 ≤ F x) ∧
      (∀ t, F 0 < t → ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      ∀ μ : ℝ, 0 < μ → ¬ (RadialHessian.matrix F 0 - μ • (1 : Mat 2)).PosSemidef :=
  BfgsCoverage.Article.Local.strict_contours_without_hessian_bound

/-- Item `C/09_C/prose/008` (`companion/chapters/09_C.tex:47`), anchor "Strong convexity of
$F$ suffices."

Under the standing assumptions of line 35, if $F$ is strongly convex (with modulus $\mu>0$ for
the Euclidean norm: $F(ax+by)\le aF(x)+bF(y)-ab\frac\mu2\norm{x-y}^2$ for $a,b\ge0$, $a+b=1$),
then the hypothesis "strictly convex positive sublevels" holds. -/
theorem strong_convexity_suffices (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b}) (μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x y : Vec 2, ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a + c = 1 →
      F (a • x + c • y) ≤ a * F x + c * F y - a * c * (μ / 2 * sqNorm (x - y))) :
    StrictlyConvexPositiveSublevels F Fstar b := by
  have hs : StrictConvexOn ℝ univ F := by
    refine ⟨convex_univ, fun x _ y _ hxy a c ha hc hac => ?_⟩
    have h := hsc x y a c ha.le hc.le hac
    have hpos : 0 < sqNorm (x - y) := lt_of_le_of_ne (sqNorm_nonneg _)
      (fun h0 => hxy (sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp h0.symm)))
    have : 0 < a * c * (μ / 2 * sqNorm (x - y)) := by positivity
    simp only [smul_eq_mul]
    linarith
  intro t _ _ x y hxy
  exact PlanarMaxRegular.no_segment_frontier_of_local_strictConvex (convex_continuous hF) hs
    (subset_univ _) x y hxy

/-- Item `C/09_C/prose/010` (`companion/chapters/09_C.tex:53`), anchor "In particular, two
different smooth branches meet transversally".

At a point $p$ with the two-branch structure of the regular-switching hypothesis (open `V ∋ p`,
convex $C^2$ branches $f_1,f_2$ on `V`, $F=\max\{f_1,f_2\}$ on `V`, both active at $p$, linearly
independent gradients): the two branches meet transversally to each other (their gradients at
$p$ are linearly independent, so $\det(\nabla f_1(p),\nabla f_2(p))\ne0$ and in particular
$\nabla f_1(p)\ne\nabla f_2(p)$), and their meeting curve is transversal to the levels: there is
a $C^2$ curve $c$ with $c(F(p))=p$ along which $f_1(c(t))=f_2(c(t))=F(c(t))=t$ for $t$ near
$F(p)$, whose velocity has unit pairing with both gradients, so it crosses every nearby level
with nonzero speed. -/
theorem branches_meet_transversally {F : Vec 2 → ℝ} {p : Vec 2} (V : Set (Vec 2))
    (hV : IsOpen V) (hp : p ∈ V) (f₁ f₂ : Vec 2 → ℝ) (_hc₁ : ConvexOn ℝ V f₁)
    (_hc₂ : ConvexOn ℝ V f₂) (hf₁ : ContDiffOn ℝ 2 f₁ V) (hf₂ : ContDiffOn ℝ 2 f₂ V)
    (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z)) (h₁ : f₁ p = F p) (h₂ : f₂ p = F p)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]) :
    HomogeneousPlanar.pairDet (coordinateGradient f₁ p) (coordinateGradient f₂ p) ≠ 0 ∧
      coordinateGradient f₁ p ≠ coordinateGradient f₂ p ∧
      ∃ c : ℝ → Vec 2, c (F p) = p ∧ ContDiffAt ℝ 2 c (F p) ∧
        ∀ᶠ t in 𝓝 (F p), f₁ (c t) = t ∧ f₂ (c t) = t ∧ F (c t) = t ∧
          dot (coordinateGradient f₁ (c t)) (deriv c t) = 1 ∧
          dot (coordinateGradient f₂ (c t)) (deriv c t) = 1 := by
  have hdet := BfgsCoverage.Article.Local.pairDet_ne_zero_of_linearIndependent hind
  refine ⟨hdet, fun heq => hdet ?_, ?_⟩
  · rw [heq]
    simp only [HomogeneousPlanar.pairDet]
    ring
  · obtain ⟨c, hc, hcC, hev⟩ := BfgsCoverage.Article.Local.corner_moves_with_level V hV hp f₁ f₂
      hf₁ hf₂ hmax h₁ h₂ hind
    refine ⟨c, hc, hcC, ?_⟩
    filter_upwards [hev] with t ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1⟩

open AffineCriticalObjective in
/-- Item `C/09_C/theorem/C:thm:cluster` (`companion/chapters/09_C.tex:55-57`), Theorem
`C:thm:cluster` ("Forced affine-critical cluster point").

Under the hypotheses of §1: $F:\R^2\to\R$ finite and convex, attaining $F_*$
(`IsLeast (range F) Fstar`), with compact sublevel $K=\{F\le b\}$, $b>F_*$ (display
`C/09_C/disp/001`); strictly convex positive sublevels (`hstrict`, i.e.
`StrictlyConvexPositiveSublevels F Fstar b`); regular switching away from affine criticality
(`hreg`, i.e. `RegularSwitching F b`, with display `C/09_C/disp/003`). Every infinite admissible
full-BFGS run (`AdmissibleBFGSRun 2 F`) starting in $K$ has at least one affine-critical cluster
point (`MapClusterPt p atTop R.x`). The second sentence ("No iterate limit, bounded condition
number, limiting eigenspace, matrix accuracy at initialization, or finite path length is
assumed") is the absence of such hypotheses. -/
theorem cluster (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b}) :
    ∃ p, MapClusterPt p atTop R.x ∧ IsAffineCritical F p :=
  BfgsCoverage.Article.Local.planar_cluster F hF Fstar hFstar b hb hK hstrict hreg R hR

/-- Item `C/09_C/disp/005` (`companion/chapters/09_C.tex:65-69`), equation `C:eq:bfgs`.

Along every admissible run, with $s_k=-\alpha_kH_kg_k$, $y_k=g_{k+1}-g_k$ and $t_k=y_k^Ts_k$
(variables with their defining equations), the matrices satisfy the usual full inverse update
\[ H_{k+1}=\Bigl(I-\frac{s_ky_k^T}{t_k}\Bigr)H_k\Bigl(I-\frac{y_ks_k^T}{t_k}\Bigr)
     +\frac{s_ks_k^T}{t_k},\qquad t_k>0. \]
(`(t k)⁻¹` is Lean's total inverse; it is $1/t_k$ since $t_k>0$.) -/
theorem update_curvature {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F) (s y : ℕ → Vec 2)
    (t : ℕ → ℝ) (hs : ∀ k, s k = -R.α k • (R.H k *ᵥ R.g k))
    (hy : ∀ k, y k = R.g (k + 1) - R.g k) (ht : ∀ k, t k = dot (y k) (s k)) (k : ℕ) :
    R.H (k + 1) = (1 - (t k)⁻¹ • outer (s k) (y k)) * R.H k * (1 - (t k)⁻¹ • outer (y k) (s k)) +
        (t k)⁻¹ • outer (s k) (s k) ∧ 0 < t k := by
  have hsk : s k = bfgsStep (R.H k) (R.g k) (R.α k) := hs k
  refine ⟨?_, ?_⟩
  · rw [R.update k, ht k, hsk, hy k]
    rfl
  · rw [ht k, hy k, hsk]
    exact R.curvature_pos k

/-- Items `C/09_C/prose/013` and `C/09_C/prose/014` (`companion/chapters/09_C.tex:70`),
anchors "The positivity $t_k>0$ in the update is derived" and "The full update then preserves
positive definiteness".

"$H_k\succ0$ and $g_k\ne0$ give $q_k=g_k^TH_kg_k>0$, and weak Wolfe gives
$t_k\ge(1-c_2)\alpha_kq_k>0$. The full update then preserves positive definiteness, starting
from $H_0\succ0$." For every positive definite $H$ and $g\ne0$, $g^THg>0$; along every admissible
run (whose definition assumes only $H_0\succ0$), every $H_k$ is positive definite and
$t_k\ge(1-c_2)\alpha_kq_k>0$, with $s_k,y_k,t_k$ as in display `C/09_C/disp/005`. -/
theorem curvature_derived {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F) (s y : ℕ → Vec 2)
    (t : ℕ → ℝ) (hs : ∀ k, s k = -R.α k • (R.H k *ᵥ R.g k))
    (hy : ∀ k, y k = R.g (k + 1) - R.g k) (ht : ∀ k, t k = dot (y k) (s k)) :
    (∀ (H : Mat 2) (g : Vec 2), H.PosDef → g ≠ 0 → 0 < dot g (H *ᵥ g)) ∧
      (∀ k, (R.H k).PosDef) ∧
      ∀ k, 0 < R.q k ∧ (1 - R.c₂) * (R.α k * R.q k) ≤ t k ∧ 0 < (1 - R.c₂) * (R.α k * R.q k) := by
  refine ⟨fun H g hH hg => ?_, R.positive_definite, fun k => ⟨R.q_pos k, ?_, ?_⟩⟩
  · have h := hH.2 g hg
    simpa only [star_trivial, dot, dotProduct] using h
  · rw [ht k, hy k, hs k]
    exact R.curvature_lower_bound k
  · exact mul_pos R.wolfe_constant_pos (R.d_pos k)

open AffineCriticalObjective in
/-- Item `C/09_C/corollary/C:cor:AC` (`companion/chapters/09_C.tex:72-74`), Corollary
`C:cor:AC` ("No false affine criticality gives convergence"), first two sentences.

Under the hypotheses of Theorem `C:thm:cluster`, if in addition
$\mathcal C_{\rm aff}\cap K\subseteq\arg\min F$, then every admissible run starting in $K$
satisfies $F(x_k)\to F_*$ and $\dist(x_k,\arg\min F)\to0$ (Euclidean distance,
`euclideanSolutionDistance`); a unique minimizer ($\arg\min F=\{x_*\}$) gives convergence of the
entire iterate sequence. The third sentence (the local version) is `cor_AC_local`. -/
theorem cor_AC (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (hcorr : {p | IsAffineCritical F p} ∩ {x | F x ≤ b} ⊆ argmin F) :
    (∀ R : AdmissibleBFGSRun 2 F, R.x 0 ∈ {x | F x ≤ b} →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
        Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0)) ∧
      ∀ xstar : Vec 2, argmin F = {xstar} → ∀ R : AdmissibleBFGSRun 2 F,
        R.x 0 ∈ {x | F x ≤ b} → Tendsto R.x atTop (𝓝 xstar) := by
  refine ⟨fun R hR => ?_, fun xstar hxs R hR => ?_⟩
  · obtain ⟨h1, h2, -⟩ := BfgsCoverage.Article.Local.planar_convergence F hF Fstar hFstar b hb hK
      hstrict hreg hcorr R hR
    exact ⟨h1, h2⟩
  · exact (BfgsCoverage.Article.Local.planar_convergence F hF Fstar hFstar b hb hK hstrict hreg
      hcorr R hR).2.2 xstar hxs

open AffineCriticalObjective in
/-- Item `C/09_C/corollary/C:cor:AC` (`companion/chapters/09_C.tex:72-74`), third sentence: "A
local version holds when the hypotheses hold only on a sufficiently low compact sublevel inside
a structural neighborhood of a unique minimizer."

Let $F$ be finite and convex with a unique minimizer $x_*$, and let $\Omega\ni x_*$ be an open
structural neighborhood on which the regular-switching alternative holds away from
$\mathcal C_{\rm aff}$ and $\mathcal C_{\rm aff}\cap\Omega\subseteq\arg\min F$; suppose the low
positive sublevels are strictly convex ($F_*<t\le b$, $F_*=F(x_*)$). Then some $\varepsilon>0$
gives $F(x_0)<F_*+\varepsilon\Rightarrow F(x_k)\to F_*$, $x_k\to x_*$ for every admissible run
(the sufficiently low sublevel $\{F\le F_*+\varepsilon\}$ is compact and lies in $\Omega$, as
the proof of the corollary explains). -/
theorem cor_AC_local (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (hxΩ : xstar ∈ Ω)
    (hreg : ∀ p ∈ Ω, ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (hcorr : {p | IsAffineCritical F p} ∩ Ω ⊆ argmin F)
    (b : ℝ) (hb : F xstar < b)
    (hstrict : ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F xstar + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) :=
  PlanarConvergence.local_convergence_basin hF xstar hmin huniq hΩ hxΩ
    (fun p hp hn => BfgsCoverage.Article.Local.regular_of_paper (hreg p hp hn))
    (fun _ hp hc => ConvexSubdifferential.zero_mem_iff_global_minimum.mpr (hcorr ⟨hc, hp⟩))
    hb hstrict

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `C/09_C/corollary/C:cor:max` (`companion/chapters/09_C.tex:76-91`), Corollary
`C:cor:max` ("Nondegenerate planar smooth maxima"), with its displays `C/09_C/disp/006`
(lines 78-80), `C/09_C/disp/007` (`C:eq:nondeg`, lines 82-85) and `C/09_C/disp/008`
(lines 87-89).

Let $F:\R^2\to\R$ be finite and convex with a unique minimizer $x_*$; near $x_*$ (on an open
$U\ni x_*$) $F=\max_{i\le m}f_i$ (`IsGreatest`) with convex $C^2$ branches; sufficiently low
positive sublevels are strictly convex (`hcontour`); $I_*=\{i:f_i(x_*)=F(x_*)\}$ is the active
set, its gradients are affinely independent and admit weights $\lambda_i^*>0$,
$\sum\lambda_i^*=1$, $\sum\lambda_i^*\nabla f_i(x_*)=0$. Then some $\varepsilon>0$ satisfies
$F(x_0)<F_*+\varepsilon\Rightarrow x_k\to x_*$ ($F_*=F(x_*)$) for every infinite admissible
full-BFGS run: arbitrary $H_0\succ0$ and valid constants, the basin chosen before the run
(quantifier order `∃ ε, ∀ R`). The last sentence is `cor_max_hessian`. -/
theorem cor_max (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (hcontour : ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (I : Finset (Fin m)) (hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F xstar + ε →
      Tendsto R.x atTop (𝓝 xstar) := by
  obtain ⟨ε, hε, h⟩ := BfgsCoverage.Article.Local.planar_max F hF xstar hmin huniq f U hU hxU hf
    hmax hcontour I hI hind lam hpos hsum hzero
  exact ⟨ε, hε, fun R hR => (h R hR).2⟩

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `C/09_C/corollary/C:cor:max` (`companion/chapters/09_C.tex:76-91`), last sentence: "A
simple sufficient replacement for the strictly convex-sublevel hypothesis is a common positive
lower Hessian bound on the finitely many locally relevant branches."

The corollary with the contour hypothesis replaced by $\nabla^2f_i(x)-\mu I\succeq0$ for the
active branches $i\in I_*$ and $x\in U$, $\mu>0$ (`RadialHessian.matrix f x` is the matrix of
the second derivative; the inactive branches are irrelevant near $x_*$). -/
theorem cor_max_hessian (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (I : Finset (Fin m)) (hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0) (μ : ℝ) (hμ : 0 < μ)
    (hhess : ∀ i ∈ I, ∀ x ∈ U, (RadialHessian.matrix (f i) x - μ • (1 : Mat 2)).PosSemidef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F xstar + ε →
      Tendsto R.x atTop (𝓝 xstar) :=
  cor_max F hF xstar hmin huniq f U hU hxU hf hmax
    (BfgsCoverage.Article.Local.planar_max_hessian_contours F hF xstar hmin huniq f U hU hxU hf
      hmax I hI hind lam hpos hsum hzero μ hμ hhess) I hI hind lam hpos hsum hzero

/-! ### §2. Why one affine-critical cluster point is enough (lines 103-121) -/

/-- Item `C/09_C/prose/018` (`companion/chapters/09_C.tex:104`), anchor "Armijo makes the
objective values decrease to a limit".

"Armijo makes the objective values decrease to a limit $\ell\ge F_*$. Every cluster point has
value $\ell$. If any cluster point is stationary, then $\ell=F_*$. Compactness gives distance to
the solution set tending to zero; uniqueness gives whole-sequence convergence." Under the
standing assumptions of line 35, for every admissible run starting in $K$: the values are
nonincreasing and converge to some $\ell\ge F_*$, every cluster point has value $\ell$, and if
some cluster point $p$ is stationary ($0\in\partial F(p)$), then $\ell=F_*$,
$\dist(x_k,\arg\min F)\to0$ (Euclidean) and, if $\arg\min F=\{x_*\}$, $x_k\to x_*$. -/
theorem one_cluster_point_enough (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b}) (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b}) :
    ∃ ℓ : ℝ, Fstar ≤ ℓ ∧ Antitone (fun k => F (R.x k)) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) ∧
      (∀ p, MapClusterPt p atTop R.x → F p = ℓ) ∧
      ((∃ p, MapClusterPt p atTop R.x ∧ (0 : Vec 2) ∈ ConvexSubdifferential.subdifferential F p) →
        ℓ = Fstar ∧ Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
        ∀ xstar : Vec 2, argmin F = {xstar} → Tendsto R.x atTop (𝓝 xstar)) := by
  obtain ⟨⟨star, hstar⟩, hlow⟩ := hFstar
  have hmin : ∀ z, F star ≤ F z := fun z => hstar ▸ hlow ⟨z, rfl⟩
  have hxK : ∀ k, R.x k ∈ {x | F x ≤ b} := fun k =>
    le_trans (R.objective_le_initial k) hR
  have hbdd : BddBelow (Set.range fun k => F (R.x k)) :=
    ⟨Fstar, by rintro _ ⟨k, rfl⟩; exact hstar ▸ hmin _⟩
  have hlim := tendsto_atTop_ciInf R.objective_antitone hbdd
  set ℓ := ⨅ k, F (R.x k) with hℓdef
  have hℓ : Fstar ≤ ℓ := le_ciInf fun k => hstar ▸ hmin _
  have hval : ∀ p, MapClusterPt p atTop R.x → F p = ℓ := fun p hp => R.value_of_cluster hlim hp
  refine ⟨ℓ, hℓ, R.objective_antitone, hlim, hval, fun ⟨p, hp, h0⟩ => ?_⟩
  have hpmin : ∀ z, F p ≤ F z := ConvexSubdifferential.zero_mem_iff_global_minimum.mp h0
  have hpℓ : F p = ℓ := hval p hp
  have hpF : F p = Fstar := le_antisymm (hstar ▸ hpmin star) (hlow ⟨p, rfl⟩)
  have hv : Tendsto (fun k => F (R.x k)) atTop (𝓝 (F p)) := by rwa [hpℓ]
  refine ⟨hpℓ.symm.trans hpF, euclidean_distance_to_argmin_of_values (convex_continuous hF) p
    hpmin hK hxK hv, fun xstar hxs => ?_⟩
  have hxsmin : ∀ z, F xstar ≤ F z := by
    have : xstar ∈ argmin F := by rw [hxs]; rfl
    exact this
  have hpx : p = xstar := by
    have : p ∈ argmin F := hpmin
    rw [hxs] at this
    exact this
  subst hpx
  refine R.iterates_tendsto_unique_min_of_values p hpmin (fun z hz => ?_) hv
  have hz' : z ∈ argmin F := fun y => hz ▸ hpmin y
  rw [hxs] at hz'
  exact hz'

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/disp/009` (`companion/chapters/09_C.tex:107-109`), equation `C:eq:AC`: the
geometric condition
\[ 0\in\aff\partial F(p)\ \Longrightarrow\ 0\in\partial F(p). \]
Unfolding theorem: the library's `AffineCriticalObjective.AffineCorrectAt F p` is this condition
at $p$. -/
theorem affineCorrectAt_iff (F : Vec 2 → ℝ) (p : Vec 2) :
    AffineCorrectAt F p ↔
      ((0 : Vec 2) ∈ affineSpan ℝ (subdifferential F p) → (0 : Vec 2) ∈ subdifferential F p) := by
  rw [AffineCorrectAt, isAffineCritical_iff_coordinate_affineSpan]

open AffineCriticalObjective in
/-- Item `C/09_C/prose/019` (`companion/chapters/09_C.tex:106-110`), anchor "therefore reduces
the problem to Theorem".

"The geometric condition \eqref{C:eq:AC} therefore reduces the problem to Theorem
`C:thm:cluster`." Under the standing assumptions of line 35, if \eqref{C:eq:AC} holds at every
point of $K$ and an admissible run starting in $K$ has an affine-critical cluster point (the
conclusion of the theorem), then $F(x_k)\to F_*$, $\dist(x_k,\arg\min F)\to0$ and, under
uniqueness, $x_k\to x_*$. -/
theorem reduction_to_cluster (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b}) (hAC : ∀ p ∈ {x | F x ≤ b}, AffineCorrectAt F p)
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b}) (p : Vec 2)
    (hp : MapClusterPt p atTop R.x) (ha : IsAffineCritical F p) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ∀ xstar : Vec 2, argmin F = {xstar} → Tendsto R.x atTop (𝓝 xstar) := by
  have hxK : ∀ k, R.x k ∈ {x | F x ≤ b} := fun k =>
    le_trans (R.objective_le_initial k) hR
  obtain ⟨hpmin, hv, -, hd, hu⟩ := R.convergence_of_affineCritical_cluster hK hxK hAC p hp ha
  obtain ⟨⟨star, hstar⟩, hlow⟩ := hFstar
  have hpF : F p = Fstar := le_antisymm (hstar ▸ hpmin star) (hlow ⟨p, rfl⟩)
  refine ⟨hpF ▸ hv, hd, fun xstar hxs => ?_⟩
  have hpx : p = xstar := by
    have : p ∈ argmin F := hpmin
    rw [hxs] at this
    exact this
  subst hpx
  refine hu (fun z hz => ?_)
  have hz' : z ∈ argmin F := fun y => hz ▸ hpmin y
  rw [hxs] at hz'
  exact hz'

open ConvexSubdifferential in
/-- Item `C/09_C/disp/010` (`companion/chapters/09_C.tex:113-115`): "if $a(p)$ is the
minimum-norm point of $\aff\partial F(p)$, then
\[ g^Ta(p)=\norm{a(p)}^2\qquad(g\in\partial F(p)). \]"
For finite convex $F:\R^2\to\R$ and every $p$ (affine critical or not): $\aff\partial F(p)$ has a
unique point $a(p)$ of least Euclidean norm, and every such point satisfies
$g^Ta(p)=\norm{a(p)}^2$ for all $g\in\partial F(p)$. -/
theorem min_norm_pairing (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (p : Vec 2) :
    (∃! a : Vec 2, a ∈ affineSpan ℝ (subdifferential F p) ∧
      ∀ c ∈ affineSpan ℝ (subdifferential F p), sqNorm a ≤ sqNorm c) ∧
    ∀ a : Vec 2, a ∈ affineSpan ℝ (subdifferential F p) →
      (∀ c ∈ affineSpan ℝ (subdifferential F p), sqNorm a ≤ sqNorm c) →
      ∀ g ∈ subdifferential F p, dot g a = sqNorm a := by
  set S := affineSpan ℝ (subdifferential F p) with hS
  have hpairing : ∀ a ∈ S, (∀ c ∈ S, sqNorm a ≤ sqNorm c) →
      ∀ g ∈ subdifferential F p, dot g a = sqNorm a := by
    intro a ha hmin g hg
    have h := BfgsCoverage.Article.Local.least_norm_orthogonal S ha hmin (subset_affineSpan ℝ _ hg)
    rw [BfgsCoverage.Article.Local.dot_comm' g a, ← BfgsCoverage.Article.Local.dot_self_eq_sqNorm]
    have h' : dot a (g - a) = dot a g - dot a a := by
      simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    linarith
  refine ⟨?_, hpairing⟩
  obtain ⟨g0, hg0⟩ := subdifferential_nonempty hF p
  have hS0 : g0 ∈ S := subset_affineSpan ℝ _ hg0
  set K := (S : Set (Vec 2)) ∩ {c | sqNorm c ≤ sqNorm g0} with hK
  have hsq_cont : Continuous (fun c : Vec 2 => sqNorm c) := by
    unfold sqNorm; fun_prop
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (AffineSubspace.closed_of_finiteDimensional S).inter
        (isClosed_le hsq_cont continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : Vec 2))
        (r := Real.sqrt (sqNorm g0))).subset ?_
      intro c hc
      rw [Metric.mem_closedBall, dist_zero_right]
      apply ConvexSubdifferential.norm_le_of_sqNorm_le (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt (sqNorm_nonneg _)]
      exact hc.2
  obtain ⟨a, haK, hamin⟩ := hKc.exists_isMinOn
    ⟨g0, hS0, show sqNorm g0 ≤ sqNorm g0 from le_rfl⟩ hsq_cont.continuousOn
  have hamin' : ∀ c ∈ S, sqNorm a ≤ sqNorm c := by
    intro c hc
    by_cases h : sqNorm c ≤ sqNorm g0
    · exact hamin ⟨hc, h⟩
    · exact (haK.2).trans (le_of_lt (lt_of_not_ge h))
  refine ⟨a, ⟨haK.1, hamin'⟩, ?_⟩
  rintro a' ⟨ha', hmin'⟩
  have h1 := BfgsCoverage.Article.Local.least_norm_orthogonal S haK.1 hamin' ha'
  have h2 := BfgsCoverage.Article.Local.least_norm_orthogonal S ha' hmin' haK.1
  have hz : sqNorm (a' - a) = 0 := by
    rw [← BfgsCoverage.Article.Local.dot_self_eq_sqNorm]
    have e1 : dot (a' - a) (a' - a) = -dot a' (a - a') - dot a (a' - a) := by
      simp only [dot, Pi.sub_apply, Finset.sum_sub_distrib.symm, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [e1, h1, h2]
    ring
  exact sub_eq_zero.mp ((CertificateGeometry.sqNorm_eq_zero_iff _).mp hz)

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/021` (`companion/chapters/09_C.tex:116`), anchor "At a
non-affine-critical point, $-a(p)/\norm{a(p)}^2$ decreases".

At $p\notin\mathcal C_{\rm aff}$ the least-norm point $a=a(p)$ of $\aff\partial F(p)$ is nonzero
and $g^T(-a/\norm{a}^2)=-1$ for every $g\in\partial F(p)$: the direction decreases every
supporting model $y\mapsto F(p)+g^T(y-p)$ at rate one. -/
theorem min_norm_rate_one (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (p : Vec 2)
    (hp : ¬ IsAffineCritical F p) (a : Vec 2) (ha : a ∈ affineSpan ℝ (subdifferential F p))
    (hmin : ∀ c ∈ affineSpan ℝ (subdifferential F p), sqNorm a ≤ sqNorm c) :
    a ≠ 0 ∧ ∀ g ∈ subdifferential F p, dot g (-(sqNorm a)⁻¹ • a) = -1 := by
  obtain ⟨hne, -, hrate⟩ := (BfgsCoverage.Article.Local.least_norm_point F hF p hp).2 a ha hmin
  exact ⟨hne, hrate⟩

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/022` (`companion/chapters/09_C.tex:116`), anchor "Thus
\eqref{C:eq:AC} says that every nonoptimal point retains equal-rate descent".

For finite convex $F$ and a set $K$ (where \eqref{C:eq:AC} is required), \eqref{C:eq:AC} at
every point of $K$ holds iff every nonoptimal point of $K$ has a direction $v$ with
$g^Tv=-1$ for all $g\in\partial F(p)$ (equal-rate descent across its supporting models). -/
theorem AC_iff_equal_rate (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (K : Set (Vec 2)) :
    (∀ p ∈ K, AffineCorrectAt F p) ↔
      ∀ p ∈ K, p ∉ argmin F → ∃ v : Vec 2, ∀ g ∈ subdifferential F p, dot g v = -1 :=
  ⟨fun h p hp => (affineCorrectAt_iff_nonoptimal_equal_rate hF p).mp (h p hp),
    fun h p hp => (affineCorrectAt_iff_nonoptimal_equal_rate hF p).mpr (h p hp)⟩

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/023` (`companion/chapters/09_C.tex:116`), anchor "It does not say
that the gradients at differentiable accepted points tend to zero."

\eqref{C:eq:AC} does not force vanishing accepted gradients: for $F(u,v)=u^2+|v|$
(`UnexcitedMetric.objective`) the condition holds at every point, yet the admissible run
`UnexcitedMetric.run` (iterates $(0,(-1/2)^kv_0)$) has $\norm{g_k}=1$ for all $k$, so
$g_k\not\to0$. -/
theorem AC_without_vanishing_gradients :
    ∃ (F : Vec 2 → ℝ) (R : AdmissibleBFGSRun 2 F), (∀ p, AffineCorrectAt F p) ∧
      (∀ k, sqNorm (R.g k) = 1) ∧ ¬ Tendsto R.g atTop (𝓝 0) := by
  have hρ : (1 / 2 : ℝ) < (1 - 1 / 4) / (1 + 1 / 4) := by norm_num
  set R := UnexcitedMetric.run 1 (1 / 2) (1 / 2) (1 / 4) (1 / 2) one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hρ with hRdef
  have hg : ∀ k, sqNorm (R.g k) = 1 := by
    intro k
    change sqNorm (UnexcitedMetric.gradient (UnexcitedMetric.sign k)) = 1
    have h := UnexcitedMetric.sign_sq k
    simp only [sqNorm, UnexcitedMetric.gradient, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    nlinarith
  refine ⟨UnexcitedMetric.objective, R, fun p hc => ?_, hg, fun ht => ?_⟩
  · rw [BfgsCoverage.Article.Local.unexcited_affineCritical_eq_zero p hc]
    apply ConvexSubdifferential.zero_mem_iff_global_minimum.mpr
    intro z
    have h00 : UnexcitedMetric.objective 0 = 0 := by simp [UnexcitedMetric.objective]
    rw [h00]
    exact UnexcitedMetric.objective_nonneg z
  · have hc : Tendsto (fun k => sqNorm (R.g k)) atTop (𝓝 (sqNorm (0 : Vec 2))) :=
      (continuous_sqNorm.tendsto _).comp ht
    simp only [hg] at hc
    have h0 : sqNorm (0 : Vec 2) = 0 := by simp [sqNorm]
    rw [h0] at hc
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc)

/-! ### §3. Vanishing steps without an assumed iterate limit (lines 126-156) -/

/-- Item `C/09_C/disp/011` (`companion/chapters/09_C.tex:128-131`): the notation
\[ q_k=g_k^TH_kg_k,\quad d_k=-g_k^Ts_k=\alpha_kq_k,\quad \Delta_k=F(x_k)-F(x_{k+1}),\quad
   c=1-c_2>0. \]
The display defines notation and asserts $-g_k^Ts_k=\alpha_kq_k$ and $c>0$. In Lean $q_k$ is
`R.q k` and $d_k$ is `R.d k` (defined as $\alpha_kq_k$); $s_k$ and $c$ are variables with their
defining equations, and $\Delta_k$ is written out. -/
theorem notation_facts {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F) (s : ℕ → Vec 2)
    (hs : ∀ k, s k = -R.α k • (R.H k *ᵥ R.g k)) (c : ℝ) (hc : c = 1 - R.c₂) (k : ℕ) :
    R.q k = dot (R.g k) (R.H k *ᵥ R.g k) ∧ R.d k = -dot (R.g k) (s k) ∧
      -dot (R.g k) (s k) = R.α k * R.q k ∧ 0 < c := by
  have hsk : s k = R.displacement k := hs k
  obtain ⟨-, hq, hd, hdα⟩ := BfgsCoverage.Article.Energy.notation_display R k
  rw [hsk]
  exact ⟨hq, hd, hdα, hc ▸ R.wolfe_constant_pos⟩

/-- Item `C/09_C/disp/012` (`companion/chapters/09_C.tex:133-135`), equation
`C:eq:eligible`: "Convexity and \eqref{C:eq:AW} give
\[ d_k>0,\qquad c_1d_k\le\Delta_k\le d_k,\qquad t_k\ge c d_k." \]
For every admissible run and every $k$, with $s_k,y_k,t_k,\Delta_k,c$ as variables with their
defining equations. -/
theorem accepted_eligible {F : Vec 2 → ℝ} (R : AdmissibleBFGSRun 2 F) (s y : ℕ → Vec 2)
    (hs : ∀ k, s k = -R.α k • (R.H k *ᵥ R.g k)) (hy : ∀ k, y k = R.g (k + 1) - R.g k)
    (t : ℕ → ℝ) (ht : ∀ k, t k = dot (y k) (s k)) (Δ : ℕ → ℝ)
    (hΔ : ∀ k, Δ k = F (R.x k) - F (R.x (k + 1))) (c : ℝ) (hc : c = 1 - R.c₂) (k : ℕ) :
    0 < R.d k ∧ R.c₁ * R.d k ≤ Δ k ∧ Δ k ≤ R.d k ∧ t k ≥ c * R.d k := by
  obtain ⟨h1, h2⟩ := R.predicted_decrease_bounds k
  refine ⟨R.d_pos k, hΔ k ▸ h1, hΔ k ▸ h2, ?_⟩
  rw [ht k, hy k, hs k, hc]
  exact R.curvature_lower_bound k

/-- Item `C/09_C/prose/024` (`companion/chapters/09_C.tex:136`), anchor "In particular
$\sum_k d_k<\infty$."

Under the standing assumptions of line 35, every admissible run starting in $K$ has summable
$d_k$, with $\sum_kd_k\le(F(x_0)-F_*)/c_1$. -/
theorem summable_d (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b}) (R : AdmissibleBFGSRun 2 F) (_hR : R.x 0 ∈ {x | F x ≤ b}) :
    Summable R.d ∧ ∑' k, R.d k ≤ (F (R.x 0) - Fstar) / R.c₁ := by
  have hL : ∀ k, Fstar ≤ F (R.x k) := fun k => hFstar.2 ⟨R.x k, rfl⟩
  have hs := R.summable_predicted_decreases_of_lower_bound Fstar hL
  refine ⟨hs, hs.tsum_le_of_sum_range_le fun N => ?_⟩
  simpa using R.finite_budget_le Fstar hL 0 N

open ConvexSubdifferential in
/-- Item `C/09_C/prose/025` (`companion/chapters/09_C.tex:136`), anchor "A finite convex
function has bounded subgradients on a compact set".

For finite convex $F:\R^n\to\R$ and compact $K$, there is $G>0$ with $\norm{g}\le G$
(Euclidean) for every $x\in K$ and every $g\in\partial F(x)$. (The library proof compares
supporting planes at $x\in K$ with the values of $F$ on a fixed enlarged compact set, as the TeX
says.) -/
theorem bounded_subgradients {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (K : Set (Vec n)) (hK : IsCompact K) :
    ∃ G : ℝ, 0 < G ∧ ∀ x ∈ K, ∀ g ∈ subdifferential F x, ‖euclideanVector g‖ ≤ G := by
  obtain ⟨G, hG, hb⟩ := convex_supporting_bound_on_compact hF hK
  refine ⟨G, hG, fun x hx g hg => ?_⟩
  have h1 := hb x hx g hg
  rw [← BfgsCoverage.Article.Local.euclid_norm_sq] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hG.le two_ne_zero).mp h1

/-- Item `C/09_C/prose/026` (`companion/chapters/09_C.tex:136`), anchor "Hence the
accepted gradients are bounded, and Chapter~\ref{comp:M} applies."

Under the standing assumptions of line 35, for every admissible run starting in $K$: the
accepted gradients are bounded, $d_k\to0$, and therefore the reciprocal-growth conclusion of
Chapter M holds (the average of $1/q_k$ diverges; article Theorem `art:reciprocal-growth`,
`Energy.reciprocal_growth`). -/
theorem gradients_bounded_M_applies (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b}) (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b}) :
    (∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ) ∧ Tendsto R.d atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop := by
  have hxK : ∀ k, R.x k ∈ {x | F x ≤ b} := fun k =>
    le_trans (R.objective_le_initial k) hR
  obtain ⟨G, hG, hgG⟩ := R.bounded_gradients_of_compact_set _ hK hxK
  have hbdd : ∃ Λ : ℝ, ∀ k, ‖euclideanVector (R.g k)‖ ≤ Λ := by
    refine ⟨G, fun k => ?_⟩
    have h1 := hgG k
    rw [← BfgsCoverage.Article.Local.euclid_norm_sq] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hG.le two_ne_zero).mp h1
  have hd := (summable_d F hF Fstar hFstar b hb hK R hR).1.tendsto_atTop_zero
  exact ⟨hbdd, hd, (BfgsCoverage.Article.Energy.reciprocal_growth R hbdd hd).2⟩

/-- Item `C/09_C/lemma/C:lem:steps` (`companion/chapters/09_C.tex:138-140`), Lemma
`C:lem:steps` ("Strict contours force vanishing steps").

Under the standing assumptions of line 35 (in particular the compactness that the proof uses),
for an admissible run starting in $K$: if $F(x_k)\downarrow\ell>F_*$ and $K_\ell=\{F\le\ell\}$
is strictly convex (no nontrivial segment in its boundary), then $s_k=-\alpha_kH_kg_k\to0$.
(Under line 35 every sublevel of $F$ is compact, by convexity, so the compactness holds for every
run; the restriction to runs starting in $K$ is the reading "the runs of §§1-3".) -/
theorem steps (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b}) (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b})
    (ℓ : ℝ) (_hdec : Antitone fun k => F (R.x k))
    (hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) (hℓpos : Fstar < ℓ)
    (hKℓ : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ ℓ} → x = y) :
    Tendsto (fun k => -R.α k • (R.H k *ᵥ R.g k)) atTop (𝓝 0) := by
  have hinit : IsCompact R.initialSublevel :=
    hK.of_isClosed_subset (isClosed_le (convex_continuous hF) continuous_const)
      (fun x (hx : F x ≤ F (R.x 0)) => (le_trans hx hR : F x ≤ b))
  obtain ⟨⟨star, hstar⟩, -⟩ := hFstar
  exact R.steps_tendsto_zero_of_strict_contour hinit ℓ hℓ ⟨star, hstar ▸ hℓpos⟩ hKℓ

/-- Item `C/09_C/disp/013` (`companion/chapters/09_C.tex:143-147`), in the proof of Lemma
`C:lem:steps`: "For every $0\le\theta\le1$, the supporting inequality at the accepted point
$x_k$ and convexity give
\[ F(x_k)-\theta d_k\le F((1-\theta)x_k+\theta x_{k+1})\le(1-\theta)F(x_k)+\theta F(x_{k+1})." \]
Under the assumptions of the lemma; the proof uses it along a subsequence with $x_k\to x$,
$x_{k+1}\to z\ne x$, and it holds for every $k$. -/
theorem steps_segment_values (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b}) (R : AdmissibleBFGSRun 2 F) (_hR : R.x 0 ∈ {x | F x ≤ b})
    (ℓ : ℝ) (_hdec : Antitone fun k => F (R.x k))
    (_hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) (_hℓpos : Fstar < ℓ)
    (_hKℓ : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ ℓ} → x = y)
    (k : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    F (R.x k) - θ * R.d k ≤ F ((1 - θ) • R.x k + θ • R.x (k + 1)) ∧
      F ((1 - θ) • R.x k + θ • R.x (k + 1)) ≤ (1 - θ) * F (R.x k) + θ * F (R.x (k + 1)) :=
  ⟨R.segment_value_lower k (1 - θ) θ (by ring),
    R.convex.2 (mem_univ _) (mem_univ _) (sub_nonneg.mpr hθ1) hθ0 (by ring)⟩

open AffineCriticalObjective in
/-- Item `C/09_C/prose/027` (`companion/chapters/09_C.tex:151`): "We suppose, for a
contradiction, that the compact cluster set $\Gamma$ contains no affine-critical point." (Wording
point W14 applied on 15 October 2026; before "We will argue by contradiction that the compact
cluster set $\Gamma$ contains no affine-critical point.")

Under the hypotheses of Theorem `C:thm:cluster`, for an admissible run starting in $K$ whose
cluster set $\Gamma$ contains no affine-critical point (the contradiction hypothesis): $\Gamma$ is
compact and nonempty; the values converge to some $\ell$ with $F_*<\ell\le b$ and $\Gamma$ lies in
the level $\{F=\ell\}$; every point of $\Gamma$ lies in $K\setminus\mathcal C_{\rm aff}$, so the
regular-switching hypothesis applies there; and Lemma `C:lem:steps` applies: $s_k\to0$. (The
contradiction hypothesis cannot hold together with the others, which is what the proof of Theorem
`C:thm:cluster` shows: this statement is vacuous by design and records the supposition and its
first consequences.) -/
theorem contradiction_setup (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b})
    (hnoaff : ∀ p, MapClusterPt p atTop R.x → ¬ IsAffineCritical F p) :
    IsCompact {p | MapClusterPt p atTop R.x} ∧ {p | MapClusterPt p atTop R.x}.Nonempty ∧
      ∃ ℓ : ℝ, Fstar < ℓ ∧ ℓ ≤ b ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) ∧
        (∀ p, MapClusterPt p atTop R.x → F p = ℓ ∧ F p ≤ b ∧ ¬ IsAffineCritical F p ∧
          ((∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
          (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
            ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
            (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
            LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))) ∧
        Tendsto (fun k => -R.α k • (R.H k *ᵥ R.g k)) atTop (𝓝 0) := by
  have hxK : ∀ k, R.x k ∈ {x | F x ≤ b} := fun k =>
    le_trans (R.objective_le_initial k) hR
  have hΓ := ClusterSetGeometry.isCompact_clusterSet R.x hK hxK
  have hne : {p | MapClusterPt p atTop R.x}.Nonempty := by
    obtain ⟨p, -, hp⟩ := hK.exists_clusterPt (f := map R.x atTop)
      (le_principal_iff.mpr (show {x | F x ≤ b} ∈ map R.x atTop from
        mem_map.mpr (Eventually.of_forall hxK)))
    exact ⟨p, hp⟩
  obtain ⟨⟨star, hstar⟩, hlow⟩ := hFstar
  have hmin : ∀ z, F star ≤ F z := fun z => hstar ▸ hlow ⟨z, rfl⟩
  obtain ⟨ℓ, hℓpos, hℓ, hlevel⟩ := R.positive_limit_of_no_affineCritical_cluster hK hxK star hmin
    (fun p hp => hnoaff p hp)
  have hℓb : ℓ ≤ b :=
    (le_of_tendsto hℓ (Eventually.of_forall R.objective_le_initial)).trans hR
  have hℓpos' : Fstar < ℓ := hstar ▸ hℓpos
  refine ⟨hΓ, hne, ℓ, hℓpos', hℓb, hℓ, fun p hp => ?_, ?_⟩
  · have hpℓ : F p = ℓ := hlevel hp
    have hpb : F p ≤ b := hpℓ ▸ hℓb
    exact ⟨hpℓ, hpb, hnoaff p hp, hreg p hpb (hnoaff p hp)⟩
  · exact steps F hF Fstar ⟨⟨star, hstar⟩, hlow⟩ b hb hK R hR ℓ R.objective_antitone hℓ hℓpos'
      (hstrict ℓ hℓpos' hℓb)

/-! ### §4. Joining comparison directions around a regular positive level (lines 161-237)

Standing assumptions of §§4-5 (line 162 and the §1 hypotheses at the level $\ell$): $F$ finite
and convex, attaining $F_*$; a level $\ell>F_*$ whose sublevel $K_\ell$ is strictly convex
(`hstrict`, hypothesis 1 at $t=\ell$); a compact $C\subset\{F=\ell\}$ with no affine-critical
point (`hnoncrit`) satisfying the regularity hypothesis (`hregular`, in the TeX form of
`RegularSwitching`). $C$ is not assumed nonempty. -/

open AffineCriticalObjective in
/-- Item `C/09_C/prose/030` (`companion/chapters/09_C.tex:169`), anchor "Near a nonsmooth
point of $C$, $F=\max\{f_1,f_2\}$".

Under the standing assumptions of §4, at a nonsmooth point $c\in C$ ($F$ not differentiable at
$c$) the smooth alternative is impossible, so near $c$ (on an open `V ∋ c`) $F=\max\{f_1,f_2\}$
with convex $C^2$ branches active at $c$, and the matrix with rows $\nabla f_1(c)^T,\nabla
f_2(c)^T$ is nonsingular. -/
theorem nonsmooth_point_two_branch (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c) :
    ∃ V : Set (Vec 2), IsOpen V ∧ c ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
      ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
      (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ c = F c ∧ f₂ c = F c ∧
      (Matrix.of ![coordinateGradient f₁ c, coordinateGradient f₂ c]).det ≠ 0 := by
  rcases hregular c hc with ⟨V, hV, hcV, hC⟩ | ⟨V, hV, hcV, f₁, f₂, h1, h2, h3, h4, h5, h6, h7, hind⟩
  · exact absurd ((hC.contDiffAt (hV.mem_nhds hcV)).differentiableAt (by norm_num)) hcns
  · refine ⟨V, hV, hcV, f₁, f₂, h1, h2, h3, h4, h5, h6, h7, ?_⟩
    have hd := BfgsCoverage.Article.Local.pairDet_ne_zero_of_linearIndependent hind
    rw [Matrix.det_fin_two]
    simpa [HomogeneousPlanar.pairDet] using hd

open AffineCriticalObjective in
/-- Item `C/09_C/disp/014` (`companion/chapters/09_C.tex:170-172`): "The equations
\[ f_1(p)=f_2(p)=t \]
therefore define a $C^2$ point curve $p_j(t)$ near $t=\ell$."

Under the standing assumptions of §4, at a nonsmooth point $c\in C$ with the two-branch data of
the regularity hypothesis: the branch-value map $x\mapsto(f_1(x),f_2(x))$ has an invertible
derivative at $c$, and there is a curve $p$, $C^2$ at $\ell$, with $p(\ell)=c$ and
$f_1(p(t))=f_2(p(t))=t$ for $t$ near $\ell$, which near $c$ is the only solution of
$f_1=f_2$ (the article's `PlanarGeometry.corner_curve`). -/
theorem corner_curve (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c]) :
    (∃ L : Vec 2 ≃L[ℝ] Vec 2, HasFDerivAt (fun z => ![f₁ z, f₂ z]) (L : Vec 2 →L[ℝ] Vec 2) c) ∧
      ∃ p : ℝ → Vec 2, p ℓ = c ∧ ContDiffAt ℝ 2 p ℓ ∧
        (∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) ∧
        ∀ᶠ z in 𝓝 c, f₁ z = f₂ z → z = p (f₁ z) :=
  BfgsCoverage.Article.PlanarGeometry.corner_curve F hF Fstar hFstar C ℓ ⟨c, hc⟩ hCcpt hCℓ hℓ
    hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) c hc hcns
    V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind

open AffineCriticalObjective in
/-- Item `C/09_C/prose/031` (`companion/chapters/09_C.tex:173`), anchor "On the level
$\ell$, the switching point is isolated."

Under the standing assumptions of §4, every nonsmooth point $c\in C$ has a neighborhood whose
only nonsmooth point on the level $\{F=\ell\}$ is $c$. -/
theorem switching_point_isolated (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c) :
    ∀ᶠ z in 𝓝 c, F z = ℓ → ¬DifferentiableAt ℝ F z → z = c := by
  rcases BfgsCoverage.Article.PlanarGeometry.regularity_of_literal (hregular c hc) with hs | ht
  · exact absurd (hs.differentiableAt (by norm_num)) hcns
  · have h := PlanarCornerCharts.nonsmooth_level_isolated ht.to_regular
    have hcl : F c = ℓ := hCℓ hc
    rw [hcl] at h
    exact h

open AffineCriticalObjective in
/-- Item `C/09_C/prose/032` (`companion/chapters/09_C.tex:173`), anchor "Smooth points of
$C$ have smooth neighborhoods."

Under the standing assumptions of §4, every point $p\in C$ at which $F$ is differentiable has an
open neighborhood on which $F$ is $C^2$ (in particular $F$ is differentiable at every point of
it). -/
theorem smooth_point_neighborhood (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (p : Vec 2) (hp : p ∈ C) (hpd : DifferentiableAt ℝ F p) :
    ∃ W : Set (Vec 2), IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ 2 F W ∧ ∀ z ∈ W, DifferentiableAt ℝ F z := by
  rcases hregular p hp with ⟨W, hW, hpW, hC⟩ | h2
  · exact ⟨W, hW, hpW, hC, fun z hz =>
      (hC.contDiffAt (hW.mem_nhds hz)).differentiableAt (by norm_num)⟩
  · rcases BfgsCoverage.Article.PlanarGeometry.regularity_of_literal (Or.inr h2) with hs | ht
    · obtain ⟨N, hN, hCN⟩ := (BfgsCoverage.Article.PlanarGeometry.contDiffAt_two_iff F p).mp hs
      exact ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN,
        hCN.mono interior_subset, fun z hz => ((hCN.mono interior_subset).contDiffAt
          (isOpen_interior.mem_nhds hz)).differentiableAt (by norm_num)⟩
    · exact absurd hpd (PlanarCornerCharts.twoBranchRegular_not_differentiable hF ht.to_regular)

open AffineCriticalObjective in
/-- Item `C/09_C/prose/033` (`companion/chapters/09_C.tex:173`), anchor "A compactness
argument gives finitely many relevant curves".

Under the standing assumptions of §4 there are finitely many nonsmooth points $c_1,\dots,c_m$
of $C$ ("level-$\ell$ corners"), curves $p_j$ with $p_j(\ell)=c_j$, $C^2$ at $\ell$ with $C^1$
velocity, along which $F(p_j(t))=t$ for $t$ near $\ell$, and an open neighborhood $N\supseteq C$
whose nonsmooth points all lie on these curves: every $z\in N$ where $F$ is not differentiable
is $p_j(F(z))$ for some $j$. -/
theorem finitely_many_curves (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    ∃ (m : ℕ) (c : Fin m → Vec 2) (p : Fin m → ℝ → Vec 2) (N : Set (Vec 2)),
      Function.Injective c ∧ (∀ j, c j ∈ C ∧ ¬DifferentiableAt ℝ F (c j)) ∧
      (∀ x ∈ C, ¬DifferentiableAt ℝ F x → ∃ j, x = c j) ∧
      (∀ j, p j ℓ = c j ∧ ContDiffAt ℝ 2 (p j) ℓ ∧ ContDiffAt ℝ 1 (deriv (p j)) ℓ ∧
        ∀ᶠ t in 𝓝 ℓ, F (p j t) = t) ∧
      IsOpen N ∧ C ⊆ N ∧ ∀ z ∈ N, ¬DifferentiableAt ℝ F z → ∃ j, z = p j (F z) := by
  classical
  have hreg' : ∀ x ∈ C, ContDiffAt ℝ 2 F x ∨ PlanarCornerCharts.TwoBranchRegularAt F x :=
    fun x hx => (BfgsCoverage.Article.PlanarGeometry.regularity_of_literal (hregular x hx)).imp id
      (fun h => h.to_regular)
  set S : Set (Vec 2) := {x | x ∈ C ∧ ¬DifferentiableAt ℝ F x} with hSdef
  have hS : S.Finite :=
    PlanarCornerCharts.finite_nonsmooth_on_compact_level hCcpt (fun x hx => hCℓ hx) hreg'
  letI : Fintype S := hS.fintype
  let e := (Fintype.equivFin S).symm
  let c : Fin (Fintype.card S) → Vec 2 := fun i => (e i : Vec 2)
  have hc : ∀ i, c i ∈ C ∧ ¬DifferentiableAt ℝ F (c i) := fun i => (e i).property
  have hmot : ∀ i, PlanarCornerCharts.TwoBranchRegularAt F (c i) := fun i => by
    rcases hreg' (c i) (hc i).1 with hs | ht
    · exact absurd (hs.differentiableAt (by norm_num)) (hc i).2
    · exact ht
  choose f p hp0 hpC hpC1 _ hpev hpinv using fun i =>
    PlanarCornerCharts.exists_regular_corner_motion hF (hmot i)
  have hcl : ∀ i, F (c i) = ℓ := fun i => hCℓ (hc i).1
  have hW : ∀ x ∈ C, ∃ W : Set (Vec 2), IsOpen W ∧ x ∈ W ∧
      ∀ z ∈ W, ¬DifferentiableAt ℝ F z → ∃ j, z = p j (F z) := by
    intro x hx
    by_cases hd : DifferentiableAt ℝ F x
    · obtain ⟨W, hWo, hxW, -, hWd⟩ := smooth_point_neighborhood F hF Fstar hFstar C ℓ hCcpt hCℓ
        hℓ hstrict hnoncrit hregular x hx hd
      exact ⟨W, hWo, hxW, fun z hz hnd => absurd (hWd z hz) hnd⟩
    · set i := e.symm ⟨x, hx, hd⟩
      have hci : c i = x := by
        show ((e (e.symm ⟨x, hx, hd⟩) : S) : Vec 2) = x
        rw [Equiv.apply_symm_apply]
      have hev := hpinv i
      rw [hci] at hev
      obtain ⟨W, hWsub, hWo, hxW⟩ := eventually_nhds_iff.mp hev
      exact ⟨W, hWo, hxW, fun z hz hnd => ⟨i, hWsub z hz hnd⟩⟩
  choose! W hWo hxW hWp using hW
  refine ⟨Fintype.card S, c, p, ⋃ x ∈ C, W x, ?_, hc, ?_, fun j => ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro x hx hd
    refine ⟨e.symm ⟨x, hx, hd⟩, ?_⟩
    show x = ((e (e.symm ⟨x, hx, hd⟩) : S) : Vec 2)
    rw [Equiv.apply_symm_apply]
  · have h1 := hp0 j
    have h2 := hpC j
    have h3 := hpC1 j
    have h4 := hpev j
    rw [hcl j] at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4.mono fun t ht => ht.1⟩
  · exact isOpen_biUnion fun x hx => hWo x hx
  · intro x hx
    exact mem_biUnion hx (hxW x hx)
  · intro z hz hnd
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hz
    exact hWp x hx z hzx hnd

open AffineCriticalObjective in
/-- Item `C/09_C/prose/034` (`companion/chapters/09_C.tex:173`), anchor "Explicitly, an
infinite sequence of distinct level-$\ell$ corners".

Under the standing assumptions of §4, $C$ contains only finitely many level-$\ell$ corners (points
where $F$ is not differentiable): an infinite family would accumulate at a smooth chart or at a
two-branch chart with only one solution of $f_1=f_2=\ell$. -/
theorem finitely_many_level_corners (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    {p ∈ C | ¬ DifferentiableAt ℝ F p}.Finite :=
  BfgsCoverage.Article.Local.finitely_many_corners C ℓ hCcpt (fun _ hp => hCℓ hp) hregular

open AffineCriticalObjective in
/-- Item `C/09_C/disp/015` (`companion/chapters/09_C.tex:176-180`), equation `C:eq:vel`:
\[ v_j(t)=p_j'(t),\qquad \nabla f_{j,1}(p_j(t))^Tv_j(t)=\nabla f_{j,2}(p_j(t))^Tv_j(t)=1. \]
Under the standing assumptions of §4, at a nonsmooth point $c\in C$ with its two-branch data
($f_{j,1}=f_1$, $f_{j,2}=f_2$) and a curve $p_j=p$ as in display `C/09_C/disp/014`, with
$v_j=p'$ (the variable `v` with `hv : v = deriv p`): the identities hold for $t$ near $\ell$, and
$v_j$ is $C^1$ at $\ell$. -/
theorem corner_velocity (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) (v : ℝ → Vec 2) (hv : v = deriv p) :
    (∀ᶠ t in 𝓝 ℓ, dot (coordinateGradient f₁ (p t)) (v t) = 1 ∧
        dot (coordinateGradient f₂ (p t)) (v t) = 1) ∧ ContDiffAt ℝ 1 v ℓ := by
  obtain ⟨h1, h2⟩ := BfgsCoverage.Article.PlanarGeometry.corner_velocity F hF Fstar hFstar C ℓ
    ⟨c, hc⟩ hCcpt hCℓ hℓ hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) c hc hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC hpdef v hv
  exact ⟨h2, h1⟩

open AffineCriticalObjective in
/-- Item `C/09_C/prose/036` (`companion/chapters/09_C.tex:181`), anchor "This vector is
tangent to the switching curve".

"This vector is tangent to the switching curve and detects a fixed nonzero increase in the
objective. It is $C^1$ in $t$." In the setting of display `C/09_C/disp/015`: for $t$ near
$\ell$, $v_j(t)$ is the velocity of the switching curve $p_j$ ($p_j$ has derivative $v_j(t)$ at
$t$), the objective along the curve is $F(p_j(t))=t$ with derivative $1$, and both active
branches increase at unit rate along $v_j(t)$; and $v_j$ is $C^1$ at $\ell$. -/
theorem velocity_properties (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) (v : ℝ → Vec 2) (hv : v = deriv p) :
    (∀ᶠ t in 𝓝 ℓ, HasDerivAt p (v t) t ∧ F (p t) = t ∧ HasDerivAt (fun τ => F (p τ)) 1 t ∧
      dot (coordinateGradient f₁ (p t)) (v t) = 1 ∧ dot (coordinateGradient f₂ (p t)) (v t) = 1) ∧
      ContDiffAt ℝ 1 v ℓ := by
  obtain ⟨hpair, hC1⟩ := corner_velocity F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit
    hregular c hc hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC hpdef v hv
  have hpt : Tendsto p (𝓝 ℓ) (𝓝 c) := by
    simpa only [ContinuousAt, hpℓ] using hpC.continuousAt
  have hFp : ∀ᶠ t in 𝓝 ℓ, F (p t) = t := by
    filter_upwards [hpt.eventually (hV.mem_nhds hcV), hpdef] with t ht hdef
    rw [hmax _ ht, hdef.1, hdef.2, max_self]
  refine ⟨?_, hC1⟩
  filter_upwards [hpC.eventually (by norm_num), hFp.eventually_nhds, hFp, hpair] with t hct hFt hF0
    hp2
  refine ⟨?_, hF0, ?_, hp2⟩
  · rw [hv]
    exact (hct.differentiableAt (by norm_num)).hasDerivAt
  · exact (hasDerivAt_id t).congr_of_eventuallyEq (hFt.mono fun τ hτ => hτ)

/-- Along the switching curve of a corner (data as in `corner_velocity`), for $t$ near $\ell$:
$p(t)\in V$, $F=\max\{f_1,f_2\}$ near $p(t)$ with both branches active and differentiable,
$F(p(t))=t$, and both branch gradients pair to one with $p'(t)$. -/
theorem along_curve (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬AffineCriticalObjective.IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) :
    ∀ᶠ t in 𝓝 ℓ, p t ∈ V ∧ ConvexSubdifferential.LocalFiniteMax F ![f₁, f₂] (p t) ∧
      (∀ i, HasFDerivAt (![f₁, f₂] i)
        (gradientFunctional (coordinateGradient (![f₁, f₂] i) (p t))) (p t)) ∧
      (∀ i, ![f₁, f₂] i (p t) = F (p t)) ∧ F (p t) = t ∧
      dot (coordinateGradient f₁ (p t)) (deriv p t) = 1 ∧
      dot (coordinateGradient f₂ (p t)) (deriv p t) = 1 := by
  obtain ⟨hpair, -⟩ := corner_velocity F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit
    hregular c hc hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC hpdef
    (deriv p) rfl
  have hpt : Tendsto p (𝓝 ℓ) (𝓝 c) := by
    simpa only [ContinuousAt, hpℓ] using hpC.continuousAt
  filter_upwards [hpt.eventually (hV.mem_nhds hcV), hpdef, hpair] with t ht hdef hpr
  have hFt : F (p t) = t := by rw [hmax _ ht, hdef.1, hdef.2, max_self]
  refine ⟨ht, ?_, fun i => ?_, fun i => ?_, hFt, hpr⟩
  · filter_upwards [hV.mem_nhds ht] with z hz
    exact BfgsCoverage.Article.PlanarGeometry.isGreatest_of_max ![f₁, f₂] (hmax z hz)
  · fin_cases i
    · exact hasFDerivAt_coordinateGradient
        ((hC₁.contDiffAt (hV.mem_nhds ht)).differentiableAt (by norm_num))
    · exact hasFDerivAt_coordinateGradient
        ((hC₂.contDiffAt (hV.mem_nhds ht)).differentiableAt (by norm_num))
  · fin_cases i
    · show f₁ (p t) = F (p t)
      rw [hFt, hdef.1]
    · show f₂ (p t) = F (p t)
      rw [hFt, hdef.2]

open AffineCriticalObjective PlanarNormalGeometry in
/-- Item `C/09_C/prose/037` (`companion/chapters/09_C.tex:189`), anchor "the nonnegative
combinations of its two active gradients generate a closed arc".

In the setting of `corner_velocity`, for $t$ near $\ell$, with $a=\nabla f_1(p_j(t))$ and
$b=\nabla f_2(p_j(t))$: the unit directions $(ra+sb)/\norm{ra+sb}$ of the nonnegative
combinations ($r,s\ge0$, $r+s>0$) form the arc `normalSector a b`, the image of $[0,1]$ under the
continuous map $r\mapsto((1-r)a+rb)/\norm{(1-r)a+rb}$; it is compact (closed), and every element
$n$ is a unit supporting normal of $K_t=\{F\le t\}$ at $p_j(t)$: $\norm{n}=1$ and
$n^T(y-p_j(t))\le0$ for all $y\in K_t$. -/
theorem normal_arc (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) :
    ∀ᶠ t in 𝓝 ℓ,
      normalized '' {u : Vec 2 | ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ 0 < r + s ∧
          u = r • coordinateGradient f₁ (p t) + s • coordinateGradient f₂ (p t)} =
        normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)) ∧
      normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)) =
        unitBlend (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)) '' Icc 0 1 ∧
      Continuous (unitBlend (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t))) ∧
      IsCompact (normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t))) ∧
      ∀ n ∈ normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)),
        sqNorm n = 1 ∧ ∀ y, F y ≤ t → dot n (y - p t) ≤ 0 := by
  filter_upwards [along_curve F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit hregular c hc
    hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC hpdef]
    with t ⟨_, hrep, hg, hact, hFt, h1, h2⟩
  set a := coordinateGradient f₁ (p t)
  set b := coordinateGradient f₂ (p t)
  have hsec := normalSector_eq_actual_normals hF hrep hg hact
  change normalized '' ConvexSubdifferential.subdifferential F (p t) = normalSector a b at hsec
  refine ⟨?_, rfl, unitBlend_continuous a b _ h1 h2, normalSector_compact a b _ h1 h2,
    fun n hn => ⟨normalSector_norm_sq h1 h2 hn, fun y hy => ?_⟩⟩
  · ext n
    constructor
    · rintro ⟨u, ⟨r, s, hr, hs, hrs, rfl⟩, rfl⟩
      refine ⟨s / (r + s), ⟨div_nonneg hs hrs.le, (div_le_one hrs).mpr (by linarith)⟩, ?_⟩
      have hb : r • a + s • b = (r + s) • blend a b (s / (r + s)) := by
        ext i
        simp only [blend, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
      show unitBlend a b _ = normalized (r • a + s • b)
      rw [hb, BfgsCoverage.Article.PlanarGeometry.normalized_smul_of_pos hrs]
      rfl
    · rintro ⟨r, hr, rfl⟩
      exact ⟨blend a b r, ⟨1 - r, r, by linarith [hr.2], hr.1, by linarith, rfl⟩, rfl⟩
  · rw [← hsec] at hn
    obtain ⟨g, hg', rfl⟩ := hn
    have hsup := hg' y
    rw [hFt] at hsup
    have hle : dot g (y - p t) ≤ 0 := by linarith
    change dotProduct (‖euclideanVector g‖⁻¹ • g) (y - p t) ≤ 0
    rw [smul_dotProduct]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) hle

open AffineCriticalObjective PlanarNormalGeometry in
/-- Item `C/09_C/prose/038` (`companion/chapters/09_C.tex:189`), anchor "This arc has width
less than $\pi$".

In the setting of `normal_arc`, for $t$ near $\ell$: any two unit normals of the arc make an
angle less than $\pi$ (the arc has width less than $\pi$; angles between Euclidean vectors,
`InnerProductGeometry.angle`), and every unit normal $n$ in it satisfies $n^Tv_j(t)>0$, where
$v_j=p_j'$. -/
theorem normal_arc_width (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) (v : ℝ → Vec 2) (hv : v = deriv p) :
    ∀ᶠ t in 𝓝 ℓ,
      (∀ n ∈ normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)),
        ∀ n' ∈ normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)),
          InnerProductGeometry.angle (euclideanVector n) (euclideanVector n') < Real.pi) ∧
      ∀ n ∈ normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)),
        0 < dot n (v t) := by
  subst hv
  filter_upwards [along_curve F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit hregular c hc
    hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC hpdef]
    with t ⟨_, _, _, _, _, h1, h2⟩
  have hpos : ∀ n ∈ normalSector (coordinateGradient f₁ (p t)) (coordinateGradient f₂ (p t)),
      0 < dot n (deriv p t) := fun n hn => normalSector_pairing_pos h1 h2 hn
  refine ⟨fun n hn n' hn' => ?_, hpos⟩
  refine lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _) fun hpi => ?_
  obtain ⟨_, r, hr, hrn⟩ := InnerProductGeometry.angle_eq_pi_iff.mp hpi
  have hn'r : n' = r • n := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) hrn
    ext i
    have hi := congrFun h i
    simpa [euclideanVector] using hi
  have h' := hpos n' hn'
  rw [hn'r, PlanarObjectiveField.dot_smul_first] at h'
  have := hpos n hn
  nlinarith

open AffineCriticalObjective PlanarNormalGeometry ConvexSubdifferential in
/-- Item `C/09_C/prose/039` (`companion/chapters/09_C.tex:191`), anchor "The normal arcs of
distinct corners at $t=\ell$ are disjoint."

Under the standing assumptions of §4, for two distinct nonsmooth points $c\ne c'$ of $C$ with
their two-branch data, the normal arcs `normalSector` $(\nabla f_1(c),\nabla f_2(c))$ and
$(\nabla f_1'(c'),\nabla f_2'(c'))$ are disjoint. ("A shared normal would support $K_\ell$ at two
different points, making their connecting segment lie on its boundary" is
`Local.common_normal_exposes_segment`; strict convexity of $K_\ell$ excludes it.) -/
theorem normal_arcs_disjoint (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c c' : Vec 2) (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c')
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (_hf₁ : ConvexOn ℝ V f₁) (_hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (V' : Set (Vec 2)) (hV' : IsOpen V') (hcV' : c' ∈ V') (f₁' f₂' : Vec 2 → ℝ)
    (_hf₁' : ConvexOn ℝ V' f₁') (_hf₂' : ConvexOn ℝ V' f₂') (hC₁' : ContDiffOn ℝ 2 f₁' V')
    (hC₂' : ContDiffOn ℝ 2 f₂' V') (hmax' : ∀ z ∈ V', F z = max (f₁' z) (f₂' z))
    (hact₁' : f₁' c' = F c') (hact₂' : f₂' c' = F c')
    (hind' : LinearIndependent ℝ ![coordinateGradient f₁' c', coordinateGradient f₂' c']) :
    Disjoint (normalSector (coordinateGradient f₁ c) (coordinateGradient f₂ c))
      (normalSector (coordinateGradient f₁' c') (coordinateGradient f₂' c')) := by
  have hsup : ∀ (W : Set (Vec 2)) (x : Vec 2) (g₁ g₂ : Vec 2 → ℝ), IsOpen W → x ∈ W →
      ContDiffOn ℝ 2 g₁ W → ContDiffOn ℝ 2 g₂ W → (∀ z ∈ W, F z = max (g₁ z) (g₂ z)) →
      g₁ x = F x → g₂ x = F x →
      Homogeneous.Supports F x (coordinateGradient g₁ x) ∧
        Homogeneous.Supports F x (coordinateGradient g₂ x) := by
    intro W x g₁ g₂ hW hxW hg₁ hg₂ hm ha₁ ha₂
    have hrep : LocalFiniteMax F ![g₁, g₂] x := by
      filter_upwards [hW.mem_nhds hxW] with z hz
      exact BfgsCoverage.Article.PlanarGeometry.isGreatest_of_max ![g₁, g₂] (hm z hz)
    have hgr : ∀ i, HasFDerivAt (![g₁, g₂] i)
        (gradientFunctional (coordinateGradient (![g₁, g₂] i) x)) x := by
      intro i
      fin_cases i
      · exact hasFDerivAt_coordinateGradient
          ((hg₁.contDiffAt (hW.mem_nhds hxW)).differentiableAt (by norm_num))
      · exact hasFDerivAt_coordinateGradient
          ((hg₂.contDiffAt (hW.mem_nhds hxW)).differentiableAt (by norm_num))
    exact ⟨active_gradient_supports hF hrep hgr (i := 0) (mem_activeIndices.mpr ha₁),
      active_gradient_supports hF hrep hgr (i := 1) (mem_activeIndices.mpr ha₂)⟩
  obtain ⟨hs₁, hs₂⟩ := hsup V c f₁ f₂ hV hcV hC₁ hC₂ hmax hact₁ hact₂
  obtain ⟨hs₁', hs₂'⟩ := hsup V' c' f₁' f₂' hV' hcV' hC₁' hC₂' hmax' hact₁' hact₂'
  obtain ⟨hv₁, hv₂⟩ := PlanarActiveGeometry.inverse_common_rate _ _
    (BfgsCoverage.Article.Local.pairDet_ne_zero_of_linearIndependent hind)
  obtain ⟨hv₁', hv₂'⟩ := PlanarActiveGeometry.inverse_common_rate _ _
    (BfgsCoverage.Article.Local.pairDet_ne_zero_of_linearIndependent hind')
  have hcl : F c = ℓ := hCℓ hc
  have hcl' : F c' = ℓ := hCℓ hc'
  exact normalSectors_disjoint hF hne (hcl.trans hcl'.symm) (by rw [hcl]; exact hstrict)
    hs₁ hs₂ hs₁' hs₂' hv₁ hv₂ hv₁' hv₂'

/-- Item `C/09_C/prose/040` (`companion/chapters/09_C.tex:191`), anchor "The finitely many
compact arcs consequently have positive angular separation."

Finitely many pairwise disjoint compact sets $A_1,\dots,A_m$ of unit vectors (the normal arcs at
the level-$\ell$ corners: compact by `normal_arc`, disjoint by `normal_arcs_disjoint`) have
positive angular separation: some $\delta>0$ bounds below the angle between any $n\in A_i$ and
$n'\in A_j$, $i\ne j$. -/
theorem arcs_positive_separation {m : ℕ} (A : Fin m → Set (Vec 2)) (hA : ∀ j, IsCompact (A j))
    (hunit : ∀ j, ∀ n ∈ A j, sqNorm n = 1) (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → ∀ n ∈ A i, ∀ n' ∈ A j,
      δ ≤ InnerProductGeometry.angle (euclideanVector n) (euclideanVector n') := by
  classical
  set P : Set (Vec 2 × Vec 2) := ⋃ (ij : Fin m × Fin m) (_ : ij.1 ≠ ij.2), A ij.1 ×ˢ A ij.2
    with hPdef
  have hP : IsCompact P :=
    isCompact_iUnion fun ij => isCompact_iUnion fun _ => (hA ij.1).prod (hA ij.2)
  set f : Vec 2 × Vec 2 → ℝ := fun q => ‖euclideanVector q.1 - euclideanVector q.2‖ with hfdef
  have hf : Continuous f := by
    have h1 : Continuous fun q : Vec 2 × Vec 2 => euclideanVector q.1 :=
      (PiLp.continuous_equiv_symm _ _).comp continuous_fst
    have h2 : Continuous fun q : Vec 2 × Vec 2 => euclideanVector q.2 :=
      (PiLp.continuous_equiv_symm _ _).comp continuous_snd
    exact (h1.sub h2).norm
  have hchord : ∀ n n' : Vec 2, sqNorm n = 1 → sqNorm n' = 1 →
      ‖euclideanVector n - euclideanVector n'‖ ≤
        InnerProductGeometry.angle (euclideanVector n) (euclideanVector n') := by
    intro n n' hn hn'
    set u := euclideanVector n
    set w := euclideanVector n'
    have hu : ‖u‖ = 1 := by
      have h := BfgsCoverage.Article.Local.euclid_norm_sq n
      rw [hn] at h
      nlinarith [norm_nonneg u]
    have hw : ‖w‖ = 1 := by
      have h := BfgsCoverage.Article.Local.euclid_norm_sq n'
      rw [hn'] at h
      nlinarith [norm_nonneg w]
    set θ := InnerProductGeometry.angle u w
    have hcos : Real.cos θ = inner u w := by
      rw [InnerProductGeometry.cos_angle, hu, hw]
      ring
    have hsq : ‖u - w‖ ^ 2 = 2 - 2 * Real.cos θ := by
      rw [@norm_sub_sq_real, hu, hw, hcos]
      ring
    have hb := Real.one_sub_sq_div_two_le_cos (x := θ)
    have hθ : 0 ≤ θ := InnerProductGeometry.angle_nonneg u w
    have h2 : ‖u - w‖ ^ 2 ≤ θ ^ 2 := by rw [hsq]; linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hθ two_ne_zero).mp h2
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · refine ⟨1, one_pos, fun i j hij n hn n' hn' => ?_⟩
    have hmem : (n, n') ∈ P := mem_iUnion₂.mpr ⟨(i, j), hij, ⟨hn, hn'⟩⟩
    rw [hPe] at hmem
    exact absurd hmem (not_mem_empty _)
  · obtain ⟨q₀, hq₀, hmin⟩ := hP.exists_isMinOn hPne hf.continuousOn
    obtain ⟨⟨i₀, j₀⟩, hij₀, hq₀'⟩ := mem_iUnion₂.mp hq₀
    have hpos : 0 < f q₀ := by
      apply norm_pos_iff.mpr
      intro h0
      have heq : q₀.1 = q₀.2 := by
        have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) (sub_eq_zero.mp h0)
        ext k
        simpa [euclideanVector] using congrFun h k
      exact Set.disjoint_left.mp (hdisj hij₀) hq₀'.1 (heq ▸ hq₀'.2)
    refine ⟨f q₀, hpos, fun i j hij n hn n' hn' => ?_⟩
    have hmem : (n, n') ∈ P := mem_iUnion₂.mpr ⟨(i, j), hij, ⟨hn, hn'⟩⟩
    exact (hmin hmem).trans (hchord n n' (hunit i n hn) (hunit j n' hn'))

open AffineCriticalObjective PlanarNormalGeometry in
/-- Item `C/09_C/prose/041` (`companion/chapters/09_C.tex:191`), anchor "After slightly
enlarging them and shrinking the interval of $t$"; the text chooses "fixed smooth angular cutoffs
$0\le\chi_j\le1$ with disjoint supports" (the range added on 15 October 2026, wording point
W15).

Under the standing assumptions of §4, for finitely many moving normal arcs
`normalSector (a j t) (b j t)` (the active gradients $a_j(t),b_j(t)$ at $p_j(t)$ and the
velocities $v_j(t)$, continuous at $\ell$, with $a_j(\ell)^Tv_j(\ell)=b_j(\ell)^Tv_j(\ell)=1$ and
pairwise disjoint arcs at $\ell$, as established before): there are fixed smooth cutoffs
$\chi_j$ with values in $[0,1]$ and pairwise disjoint supports, and constants $\eta_j>0$, such
that for all $t$ near $\ell$ each $\chi_j$ equals one on a neighborhood of every point of the
moving arc, and $n(\theta)^Tv_j(t)\ge\eta_j$ wherever $\chi_j(n(\theta))\ne0$. The cutoffs are
ambient ($\chi_j:\R^2\to\R$); the angular cutoffs of the TeX are
$\theta\mapsto\chi_j(n(\theta))$. -/
theorem cutoffs_exist (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    {m : ℕ} (a b v : Fin m → ℝ → Vec 2) (ha : ∀ j, ContinuousAt (a j) ℓ)
    (hb : ∀ j, ContinuousAt (b j) ℓ) (hv : ∀ j, ContinuousAt (v j) ℓ)
    (hav : ∀ j, dot (a j ℓ) (v j ℓ) = 1) (hbv : ∀ j, dot (b j ℓ) (v j ℓ) = 1)
    (hdisj : Pairwise fun i j =>
      Disjoint (normalSector (a i ℓ) (b i ℓ)) (normalSector (a j ℓ) (b j ℓ))) :
    ∃ (χ : Fin m → Vec 2 → ℝ) (η : Fin m → ℝ), (∀ j, ContDiff ℝ ∞ (χ j)) ∧ (∀ j, 0 < η j) ∧
      (∀ j w, χ j w ∈ Icc (0 : ℝ) 1) ∧
      (Pairwise fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      ∀ᶠ t in 𝓝 ℓ, ∀ j, (∀ n ∈ normalSector (a j t) (b j t), ∀ᶠ z in 𝓝 n, χ j z = 1) ∧
        ∀ θ : ℝ, χ j (PlanarTransport.normal θ) ≠ 0 →
          η j ≤ dot (PlanarTransport.normal θ) (v j t) := by
  obtain ⟨χ, η, hχ, hη, h01, hsupp, hev⟩ :=
    exists_moving_normalSector_cutoffs a b v ℓ ha hb hv hav hbv hdisj
  refine ⟨χ, η, hχ, hη, h01, hsupp, ?_⟩
  filter_upwards [hev] with t ht j
  exact ⟨(ht j).1, fun θ hθ => (ht j).2 _ (PlanarTransport.normal_norm_sq θ).le hθ⟩

/-- Item `C/09_C/disp/016` (`companion/chapters/09_C.tex:194-197`): the definitions
\[ n(\theta)=(\cos\theta,\sin\theta),\qquad T(\theta)=(-\sin\theta,\cos\theta). \]
Unfolding theorem for the library's `PlanarTransport.normal` and `PlanarTransport.tangent`. -/
theorem normal_tangent_def (θ : ℝ) :
    PlanarTransport.normal θ = ![Real.cos θ, Real.sin θ] ∧
      PlanarTransport.tangent θ = ![-Real.sin θ, Real.cos θ] := ⟨rfl, rfl⟩

/-- Item `C/09_C/prose/042` (`companion/chapters/09_C.tex:202`), anchor "The supports are
disjoint, so this is a convex combination of positive numbers".

For angular cutoffs $\chi_j$ (with values in $[0,1]$, as line 191 states since 15 October 2026,
wording point W15, and pairwise disjoint supports) and velocities $v_j$, at each angle $\theta$ the
height $h(t,\theta)=1+\sum_j\chi_j(\theta)[n(\theta)^Tv_j(t)-1]$ (display `C/09_C/disp/017`) is
either $1$ (no cutoff is nonzero at $\theta$) or the convex combination
$(1-\chi_j(\theta))\cdot1+\chi_j(\theta)\,n(\theta)^Tv_j(t)$ for the only $j$ with
$\chi_j(\theta)\ne0$. If, on a set $J$ of levels, $n(\theta)^Tv_j(t)\ge\eta>0$ wherever
$\chi_j(\theta)\ne0$ (the supports chosen where $n^Tv_j>0$ uniformly) and $\norm{v_j(t)}\le B$,
then $0<\min\{1,\eta\}\le h(t,\theta)\le\max\{1,B\}$ for $t\in J$: $h$ is bounded above
and bounded away from zero. -/
theorem height_convex_combination {m : ℕ} (χ : Fin m → ℝ → ℝ)
    (hχ01 : ∀ j θ, χ j θ ∈ Icc (0 : ℝ) 1)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (J : Set ℝ) (η B : ℝ) (hη : 0 < η)
    (hpos : ∀ j θ, ∀ t ∈ J, χ j θ ≠ 0 → η ≤ dot (PlanarTransport.normal θ) (v j t))
    (hB : ∀ j, ∀ t ∈ J, ‖euclideanVector (v j t)‖ ≤ B) :
    (∀ t θ, ((∀ j, χ j θ = 0) ∧ BfgsCoverage.Article.PlanarGeometry.height χ v t θ = 1) ∨
      ∃ j, χ j θ ≠ 0 ∧ (∀ i, i ≠ j → χ i θ = 0) ∧
        BfgsCoverage.Article.PlanarGeometry.height χ v t θ =
          (1 - χ j θ) * 1 + χ j θ * dot (PlanarTransport.normal θ) (v j t)) ∧
    0 < min 1 η ∧ ∀ t ∈ J, ∀ θ, min 1 η ≤ BfgsCoverage.Article.PlanarGeometry.height χ v t θ ∧
      BfgsCoverage.Article.PlanarGeometry.height χ v t θ ≤ max 1 B := by
  have hform : ∀ t θ, ((∀ j, χ j θ = 0) ∧ BfgsCoverage.Article.PlanarGeometry.height χ v t θ = 1) ∨
      ∃ j, χ j θ ≠ 0 ∧ (∀ i, i ≠ j → χ i θ = 0) ∧
        BfgsCoverage.Article.PlanarGeometry.height χ v t θ =
          (1 - χ j θ) * 1 + χ j θ * dot (PlanarTransport.normal θ) (v j t) := by
    intro t θ
    by_cases he : ∃ j, χ j θ ≠ 0
    · obtain ⟨j, hj⟩ := he
      have hother : ∀ i, i ≠ j → χ i θ = 0 := by
        intro i hij
        by_contra hne
        exact Set.disjoint_left.mp (hχsupp hij) hne hj
      refine Or.inr ⟨j, hj, hother, ?_⟩
      unfold BfgsCoverage.Article.PlanarGeometry.height
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [hother i hij, zero_mul])
        (fun h => absurd (Finset.mem_univ j) h)]
      ring
    · push_neg at he
      refine Or.inl ⟨he, ?_⟩
      simp only [BfgsCoverage.Article.PlanarGeometry.height, he, zero_mul, Finset.sum_const_zero,
        add_zero]
  refine ⟨hform, lt_min one_pos hη, fun t ht θ => ?_⟩
  rcases hform t θ with ⟨_, h1⟩ | ⟨j, hj, _, hval⟩
  · rw [h1]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  · set d := dot (PlanarTransport.normal θ) (v j t)
    have hc := hχ01 j θ
    have hdη : η ≤ d := hpos j θ t ht hj
    have hdB : d ≤ B := by
      have hcs := PlanarCrossing.abs_dot_le_euclidean_norm (PlanarTransport.normal θ) (v j t)
      have hn : ‖euclideanVector (PlanarTransport.normal θ)‖ = 1 := by
        have h := BfgsCoverage.Article.Local.euclid_norm_sq (PlanarTransport.normal θ)
        rw [PlanarTransport.normal_norm_sq] at h
        nlinarith [norm_nonneg (euclideanVector (PlanarTransport.normal θ))]
      rw [hn, one_mul] at hcs
      exact (le_abs_self d).trans (hcs.trans (hB j t ht))
    rw [hval]
    constructor
    · have h1 : min 1 η ≤ 1 := min_le_left _ _
      have h2 : min 1 η ≤ d := (min_le_right _ _).trans hdη
      nlinarith [hc.1, hc.2]
    · have h1 : 1 ≤ max 1 B := le_max_left _ _
      have h2 : d ≤ max 1 B := hdB.trans (le_max_right _ _)
      nlinarith [hc.1, hc.2]

/-- Item `C/09_C/prose/043` (`companion/chapters/09_C.tex:202`), anchor "It is $C^1$ in $t$
and smooth in $\theta$", first part.

For smooth ambient cutoffs (angular cutoffs $\theta\mapsto\chi_j(n(\theta))$) and velocities
$v_j$ that are $C^1$ on a set $J$ of levels: $h(t,\theta)$ is $C^1$ in $t\in J$ for each $\theta$,
and $C^\infty$ in $\theta$ for each $t$. -/
theorem height_regularity {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (v : Fin m → ℝ → Vec 2) (J : Set ℝ) (hv : ∀ j, ContDiffOn ℝ 1 (v j) J) :
    (∀ θ, ContDiffOn ℝ 1 (fun t => BfgsCoverage.Article.PlanarGeometry.height
      (fun j φ => χ j (PlanarTransport.normal φ)) v t θ) J) ∧
    ∀ t, ContDiff ℝ ∞ (fun θ => BfgsCoverage.Article.PlanarGeometry.height
      (fun j φ => χ j (PlanarTransport.normal φ)) v t θ) := by
  refine ⟨fun θ => ?_, fun t => PlanarJoinedFrame.height_contDiff (fun j => v j t) hχ⟩
  unfold BfgsCoverage.Article.PlanarGeometry.height
  apply contDiffOn_const.add
  apply ContDiffOn.sum
  intro j _
  apply contDiffOn_const.mul
  apply ContDiffOn.sub _ contDiffOn_const
  have h := (gradientFunctional (PlanarTransport.normal θ)).contDiff.comp_contDiffOn (hv j)
  simpa only [Function.comp_def, gradientFunctional_apply] using h

/-- Item `C/09_C/prose/116` (`companion/chapters/09_C.tex:202`), anchor "with the mixed
derivatives used below bounded".

For smooth ambient cutoffs (angular cutoffs $\theta\mapsto\chi_j(n(\theta))$) and velocities $v_j$
with derivatives $v_j'$ on a set $J$ of levels, bounded there ($\norm{v_j}\le B$,
$\norm{v_j'}\le B'$, as on the compact level interval): one constant bounds, for all $t\in J$ and
all $\theta$, the derivatives of $h$ that the construction uses: $\partial_\theta h$,
$\partial_th$, the mixed derivative $\partial_t\partial_\theta h$ and $\partial_\theta^2h$ (which
enters $Dw$ through display `C/09_C/disp/021`). -/
theorem height_mixed_derivatives_bounded {m : ℕ} (χ : Fin m → Vec 2 → ℝ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (v v' : Fin m → ℝ → Vec 2) (J : Set ℝ)
    (hv : ∀ j, ∀ t ∈ J, HasDerivAt (v j) (v' j t) t) (B B' : ℝ)
    (hB : ∀ j, ∀ t ∈ J, ‖euclideanVector (v j t)‖ ≤ B)
    (hB' : ∀ j, ∀ t ∈ J, ‖euclideanVector (v' j t)‖ ≤ B') :
    ∃ K : ℝ, ∀ t ∈ J, ∀ θ : ℝ,
      |deriv (fun φ => BfgsCoverage.Article.PlanarGeometry.height
          (fun j ψ => χ j (PlanarTransport.normal ψ)) v t φ) θ| ≤ K ∧
      |deriv (fun τ => BfgsCoverage.Article.PlanarGeometry.height
          (fun j ψ => χ j (PlanarTransport.normal ψ)) v τ θ) t| ≤ K ∧
      |deriv (fun τ => deriv (fun φ => BfgsCoverage.Article.PlanarGeometry.height
          (fun j ψ => χ j (PlanarTransport.normal ψ)) v τ φ) θ) t| ≤ K ∧
      |deriv (fun ψ => deriv (fun φ => BfgsCoverage.Article.PlanarGeometry.height
          (fun j ψ => χ j (PlanarTransport.normal ψ)) v t φ) ψ) θ| ≤ K := by
  classical
  have hball : IsCompact (Metric.closedBall (0 : Vec 2) 1) := isCompact_closedBall 0 1
  have hχ1 : ∀ j, ContDiff ℝ 1 (fderiv ℝ (χ j)) := fun j =>
    (contDiff_infty_iff_fderiv.mp (hχ j)).2.of_le (by simp)
  choose K0 hK0 using fun j => hball.exists_bound_of_continuousOn (hχ j).continuous.continuousOn
  choose K1 hK1 using fun j =>
    hball.exists_bound_of_continuousOn ((hχ j).continuous_fderiv (by simp)).continuousOn
  choose K2 hK2 using fun j =>
    hball.exists_bound_of_continuousOn ((hχ1 j).continuous_fderiv le_rfl).continuousOn
  set A0 := ∑ j, |K0 j| with hA0
  set A1 := ∑ j, |K1 j| with hA1
  set A2 := ∑ j, |K2 j| with hA2
  have hn1 : ∀ θ, PlanarTransport.normal θ ∈ Metric.closedBall (0 : Vec 2) 1 := by
    intro θ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    fin_cases i
    · simpa [PlanarTransport.normal] using Real.abs_cos_le_one θ
    · simpa [PlanarTransport.normal] using Real.abs_sin_le_one θ
  have hT1 : ∀ θ, ‖PlanarAmbientFrame.rotate (PlanarTransport.normal θ)‖ ≤ 1 := by
    intro θ
    rw [PlanarAmbientFrame.rotate_normal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    fin_cases i
    · simpa [PlanarTransport.tangent] using Real.abs_sin_le_one θ
    · simpa [PlanarTransport.tangent] using Real.abs_cos_le_one θ
  have hEn : ∀ θ, ‖euclideanVector (PlanarTransport.normal θ)‖ = 1 := by
    intro θ
    have h := BfgsCoverage.Article.Local.euclid_norm_sq (PlanarTransport.normal θ)
    rw [PlanarTransport.normal_norm_sq] at h
    nlinarith [norm_nonneg (euclideanVector (PlanarTransport.normal θ))]
  have hET : ∀ θ, ‖euclideanVector (PlanarAmbientFrame.rotate (PlanarTransport.normal θ))‖ = 1 := by
    intro θ
    rw [PlanarAmbientFrame.rotate_normal]
    have h := BfgsCoverage.Article.Local.euclid_norm_sq (PlanarTransport.tangent θ)
    rw [PlanarTransport.tangent_norm_sq] at h
    nlinarith [norm_nonneg (euclideanVector (PlanarTransport.tangent θ))]
  have hdot : ∀ (a u : Vec 2), ‖euclideanVector a‖ = 1 → |dot a u| ≤ ‖euclideanVector u‖ := by
    intro a u ha
    have h := PlanarCrossing.abs_dot_le_euclidean_norm a u
    rwa [ha, one_mul] at h
  have hc0 : ∀ j θ, |χ j (PlanarTransport.normal θ)| ≤ |K0 j| := by
    intro j θ
    have h := hK0 j _ (hn1 θ)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_abs_self _)
  have hc1 : ∀ j θ, |(fderiv ℝ (χ j) (PlanarTransport.normal θ))
      (PlanarAmbientFrame.rotate (PlanarTransport.normal θ))| ≤ |K1 j| := by
    intro j θ
    have h1 := (fderiv ℝ (χ j) (PlanarTransport.normal θ)).le_opNorm
      (PlanarAmbientFrame.rotate (PlanarTransport.normal θ))
    have h2 := hK1 j _ (hn1 θ)
    rw [Real.norm_eq_abs] at h1
    calc _ ≤ ‖fderiv ℝ (χ j) (PlanarTransport.normal θ)‖ *
          ‖PlanarAmbientFrame.rotate (PlanarTransport.normal θ)‖ := h1
      _ ≤ |K1 j| * 1 := mul_le_mul (h2.trans (le_abs_self _)) (hT1 θ) (norm_nonneg _)
          (abs_nonneg _)
      _ = |K1 j| := mul_one _
  have hc1n : ∀ j θ, |(fderiv ℝ (χ j) (PlanarTransport.normal θ)) (-PlanarTransport.normal θ)| ≤
      |K1 j| := by
    intro j θ
    have h1 := (fderiv ℝ (χ j) (PlanarTransport.normal θ)).le_opNorm (-PlanarTransport.normal θ)
    have h2 := hK1 j _ (hn1 θ)
    have h3 : ‖PlanarTransport.normal θ‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hn1 θ
    rw [Real.norm_eq_abs, norm_neg] at h1
    calc _ ≤ ‖fderiv ℝ (χ j) (PlanarTransport.normal θ)‖ * ‖PlanarTransport.normal θ‖ := h1
      _ ≤ |K1 j| * 1 := mul_le_mul (h2.trans (le_abs_self _)) h3 (norm_nonneg _) (abs_nonneg _)
      _ = |K1 j| := mul_one _
  have hc2 : ∀ j θ, |((fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ))
      (PlanarTransport.tangent θ)) (PlanarTransport.tangent θ)| ≤ |K2 j| := by
    intro j θ
    have hT : ‖PlanarTransport.tangent θ‖ ≤ 1 := by
      have h := hT1 θ
      rwa [PlanarAmbientFrame.rotate_normal] at h
    have h1 := ((fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ))
      (PlanarTransport.tangent θ)).le_opNorm (PlanarTransport.tangent θ)
    have h1' := (fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ)).le_opNorm
      (PlanarTransport.tangent θ)
    have h2 := hK2 j _ (hn1 θ)
    rw [Real.norm_eq_abs] at h1
    calc _ ≤ ‖(fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ)) (PlanarTransport.tangent θ)‖ *
          ‖PlanarTransport.tangent θ‖ := h1
      _ ≤ (‖fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ)‖ *
          ‖PlanarTransport.tangent θ‖) * ‖PlanarTransport.tangent θ‖ :=
          mul_le_mul_of_nonneg_right h1' (norm_nonneg _)
      _ ≤ (|K2 j| * 1) * 1 := by
          gcongr
          exact h2.trans (le_abs_self _)
      _ = |K2 j| := by ring
  -- the angular derivative of h is the ambient angular slope
  have hS : ∀ τ θ, deriv (fun φ => BfgsCoverage.Article.PlanarGeometry.height
      (fun j ψ => χ j (PlanarTransport.normal ψ)) v τ φ) θ =
      PlanarAmbientFrame.angularSlope χ (fun j => v j τ) (PlanarTransport.normal θ) := fun τ θ =>
    (PlanarAmbientFrame.angularSlope_eq_deriv (fun j => v j τ)
      (fun j => (hχ j).differentiable (by simp)) θ).symm
  -- the second angular derivative of h
  have hSθ : ∀ τ θ, HasDerivAt (fun ψ =>
      PlanarAmbientFrame.angularSlope χ (fun j => v j τ) (PlanarTransport.normal ψ))
      (∑ j, ((((fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ))
          (PlanarTransport.tangent θ)) (PlanarTransport.tangent θ) +
          (fderiv ℝ (χ j) (PlanarTransport.normal θ)) (-PlanarTransport.normal θ)) *
          (dot (PlanarTransport.normal θ) (v j τ) - 1) +
          (fderiv ℝ (χ j) (PlanarTransport.normal θ)) (PlanarTransport.tangent θ) *
          dot (PlanarTransport.tangent θ) (v j τ) +
        ((fderiv ℝ (χ j) (PlanarTransport.normal θ)) (PlanarTransport.tangent θ) *
          dot (PlanarTransport.tangent θ) (v j τ) +
          χ j (PlanarTransport.normal θ) * dot (-PlanarTransport.normal θ) (v j τ)))) θ := by
    intro τ θ
    have hfun : (fun ψ =>
        PlanarAmbientFrame.angularSlope χ (fun j => v j τ) (PlanarTransport.normal ψ)) =
        fun ψ => ∑ j, ((fderiv ℝ (χ j) (PlanarTransport.normal ψ)) (PlanarTransport.tangent ψ) *
          (dot (PlanarTransport.normal ψ) (v j τ) - 1) + χ j (PlanarTransport.normal ψ) *
          dot (PlanarTransport.tangent ψ) (v j τ)) := by
      funext ψ
      simp only [PlanarAmbientFrame.angularSlope, PlanarAmbientFrame.rotate_normal]
    rw [hfun]
    have hn := PlanarTransport.normal_hasDerivAt θ
    have hT := PlanarTransport.tangent_hasDerivAt θ
    refine HasDerivAt.sum (u := Finset.univ) fun j _ => ?_
    have hc : HasDerivAt (fun ψ => fderiv ℝ (χ j) (PlanarTransport.normal ψ))
        ((fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ)) (PlanarTransport.tangent θ)) θ :=
      (((hχ1 j).differentiable le_rfl) (PlanarTransport.normal θ)).hasFDerivAt.comp_hasDerivAt θ hn
    have hχn : HasDerivAt (fun ψ => χ j (PlanarTransport.normal ψ))
        ((fderiv ℝ (χ j) (PlanarTransport.normal θ)) (PlanarTransport.tangent θ)) θ :=
      (((hχ j).differentiable (by simp)) (PlanarTransport.normal θ)).hasFDerivAt.comp_hasDerivAt θ
        hn
    have hdn : HasDerivAt (fun ψ => dot (PlanarTransport.normal ψ) (v j τ))
        (dot (PlanarTransport.tangent θ) (v j τ)) θ := by
      have h := (gradientFunctional (v j τ)).hasFDerivAt.comp_hasDerivAt θ hn
      simpa only [gradientFunctional_apply, dot, mul_comm] using h
    have hdT : HasDerivAt (fun ψ => dot (PlanarTransport.tangent ψ) (v j τ))
        (dot (-PlanarTransport.normal θ) (v j τ)) θ := by
      have h := (gradientFunctional (v j τ)).hasFDerivAt.comp_hasDerivAt θ hT
      simpa only [gradientFunctional_apply, dot, mul_comm] using h
    exact ((hc.clm_apply hT).mul (hdn.sub_const 1)).add (hχn.mul hdT)
  -- derivatives in the level
  have hdv : ∀ (a : Vec 2) j, ∀ t ∈ J, HasDerivAt (fun τ => dot a (v j τ)) (dot a (v' j t)) t := by
    intro a j t ht
    have h := (gradientFunctional a).hasFDerivAt.comp_hasDerivAt t (hv j t ht)
    simpa only [Function.comp_def, gradientFunctional_apply] using h
  have hht : ∀ t ∈ J, ∀ θ, HasDerivAt (fun τ => BfgsCoverage.Article.PlanarGeometry.height
      (fun j ψ => χ j (PlanarTransport.normal ψ)) v τ θ)
      (∑ j, χ j (PlanarTransport.normal θ) * dot (PlanarTransport.normal θ) (v' j t)) t := by
    intro t ht θ
    have h := (HasDerivAt.sum (u := Finset.univ) fun j _ =>
      ((hdv (PlanarTransport.normal θ) j t ht).sub_const 1).const_mul
        (χ j (PlanarTransport.normal θ))).const_add 1
    simpa only [BfgsCoverage.Article.PlanarGeometry.height] using h
  have hSt : ∀ t ∈ J, ∀ θ, HasDerivAt (fun τ =>
      PlanarAmbientFrame.angularSlope χ (fun j => v j τ) (PlanarTransport.normal θ))
      (∑ j, ((fderiv ℝ (χ j) (PlanarTransport.normal θ))
          (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) *
          dot (PlanarTransport.normal θ) (v' j t) + χ j (PlanarTransport.normal θ) *
          dot (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) (v' j t))) t := by
    intro t ht θ
    have h := HasDerivAt.sum (u := Finset.univ) fun j _ =>
      (((hdv (PlanarTransport.normal θ) j t ht).sub_const 1).const_mul
        ((fderiv ℝ (χ j) (PlanarTransport.normal θ))
          (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)))).add
      ((hdv (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) j t ht).const_mul
        (χ j (PlanarTransport.normal θ)))
    simpa only [PlanarAmbientFrame.angularSlope] using h
  refine ⟨A1 * (|B| + 1) + A0 * |B| + A0 * |B'| + (A1 + A0) * |B'| +
    ((A2 + A1) * (|B| + 1) + A1 * |B| + (A1 * |B| + A0 * |B|)), fun t ht θ => ?_⟩
  have hA0n : 0 ≤ A0 := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hA1n : 0 ≤ A1 := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hA2n : 0 ≤ A2 := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hBn := abs_nonneg B
  have hB'n := abs_nonneg B'
  have hvB : ∀ j, ‖euclideanVector (v j t)‖ ≤ |B| := fun j => (hB j t ht).trans (le_abs_self _)
  have hvB' : ∀ j, ‖euclideanVector (v' j t)‖ ≤ |B'| := fun j =>
    (hB' j t ht).trans (le_abs_self _)
  -- bound of the angular derivative
  have b1 : |PlanarAmbientFrame.angularSlope χ (fun j => v j t) (PlanarTransport.normal θ)| ≤
      A1 * (|B| + 1) + A0 * |B| := by
    unfold PlanarAmbientFrame.angularSlope
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hA1, hA0, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have e1 := hc1 j θ
    have e2 := hc0 j θ
    have e3 : |dot (PlanarTransport.normal θ) (v j t) - 1| ≤ |B| + 1 :=
      (abs_sub _ _).trans (by rw [abs_one]; linarith [hdot _ (v j t) (hEn θ), hvB j])
    have e4 : |dot (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) (v j t)| ≤ |B| :=
      (hdot _ _ (hET θ)).trans (hvB j)
    calc _ ≤ |(fderiv ℝ (χ j) (PlanarTransport.normal θ))
            (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) *
            (dot (PlanarTransport.normal θ) (v j t) - 1)| +
          |χ j (PlanarTransport.normal θ) *
            dot (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) (v j t)| := abs_add _ _
      _ ≤ |K1 j| * (|B| + 1) + |K0 j| * |B| := by
          rw [abs_mul, abs_mul]
          gcongr
  have b2 : |∑ j, χ j (PlanarTransport.normal θ) * dot (PlanarTransport.normal θ) (v' j t)| ≤
      A0 * |B'| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hA0, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hc0 j θ) ((hdot _ _ (hEn θ)).trans (hvB' j)) (abs_nonneg _) (abs_nonneg _)
  have b3 : |∑ j, ((fderiv ℝ (χ j) (PlanarTransport.normal θ))
          (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) *
          dot (PlanarTransport.normal θ) (v' j t) + χ j (PlanarTransport.normal θ) *
          dot (PlanarAmbientFrame.rotate (PlanarTransport.normal θ)) (v' j t))| ≤
      (A1 + A0) * |B'| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hA1, hA0, add_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (abs_add _ _).trans ?_
    rw [abs_mul, abs_mul]
    have e1 := hc1 j θ
    have e2 := hc0 j θ
    have e5 := (hdot _ _ (hEn θ)).trans (hvB' j)
    have e6 := (hdot _ _ (hET θ)).trans (hvB' j)
    gcongr
  -- bound of the second angular derivative
  have b4 : |∑ j, ((((fderiv ℝ (fderiv ℝ (χ j)) (PlanarTransport.normal θ))
          (PlanarTransport.tangent θ)) (PlanarTransport.tangent θ) +
          (fderiv ℝ (χ j) (PlanarTransport.normal θ)) (-PlanarTransport.normal θ)) *
          (dot (PlanarTransport.normal θ) (v j t) - 1) +
          (fderiv ℝ (χ j) (PlanarTransport.normal θ)) (PlanarTransport.tangent θ) *
          dot (PlanarTransport.tangent θ) (v j t) +
        ((fderiv ℝ (χ j) (PlanarTransport.normal θ)) (PlanarTransport.tangent θ) *
          dot (PlanarTransport.tangent θ) (v j t) +
          χ j (PlanarTransport.normal θ) * dot (-PlanarTransport.normal θ) (v j t)))| ≤
      (A2 + A1) * (|B| + 1) + A1 * |B| + (A1 * |B| + A0 * |B|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsum : (A2 + A1) * (|B| + 1) + A1 * |B| + (A1 * |B| + A0 * |B|) =
        ∑ j, ((|K2 j| + |K1 j|) * (|B| + 1) + |K1 j| * |B| + (|K1 j| * |B| + |K0 j| * |B|)) := by
      rw [hA2, hA1, hA0]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hsum]
    refine Finset.sum_le_sum fun j _ => ?_
    have e1 := hc1 j θ
    rw [PlanarAmbientFrame.rotate_normal] at e1
    have e2 := hc0 j θ
    have e3 : |dot (PlanarTransport.normal θ) (v j t) - 1| ≤ |B| + 1 :=
      (abs_sub _ _).trans (by rw [abs_one]; linarith [hdot _ (v j t) (hEn θ), hvB j])
    have e4 : |dot (PlanarTransport.tangent θ) (v j t)| ≤ |B| := by
      have h := (hdot _ _ (hET θ)).trans (hvB j)
      rwa [PlanarAmbientFrame.rotate_normal] at h
    have e5 : |dot (-PlanarTransport.normal θ) (v j t)| ≤ |B| := by
      have h : dot (-PlanarTransport.normal θ) (v j t) =
          -dot (PlanarTransport.normal θ) (v j t) := by
        simp [dot, Finset.sum_neg_distrib]
      rw [h, abs_neg]
      exact (hdot _ _ (hEn θ)).trans (hvB j)
    have e6 := hc2 j θ
    have e7 := hc1n j θ
    refine (abs_add _ _).trans (add_le_add ((abs_add _ _).trans (add_le_add ?_ ?_))
      ((abs_add _ _).trans (add_le_add ?_ ?_)))
    · rw [abs_mul]
      exact mul_le_mul ((abs_add _ _).trans (add_le_add e6 e7)) e3 (abs_nonneg _)
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    · rw [abs_mul]
      exact mul_le_mul e1 e4 (abs_nonneg _) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul e1 e4 (abs_nonneg _) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul e2 e5 (abs_nonneg _) (abs_nonneg _)
  have p1 : 0 ≤ A1 * (|B| + 1) := mul_nonneg hA1n (by linarith)
  have p2 : 0 ≤ A0 * |B| := mul_nonneg hA0n hBn
  have p3 : 0 ≤ A0 * |B'| := mul_nonneg hA0n hB'n
  have p4 : 0 ≤ (A1 + A0) * |B'| := mul_nonneg (by linarith) hB'n
  have p5 : 0 ≤ (A2 + A1) * (|B| + 1) + A1 * |B| + (A1 * |B| + A0 * |B|) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS t θ]
    linarith
  · rw [(hht t ht θ).deriv]
    linarith
  · have heq : (fun τ => deriv (fun φ => BfgsCoverage.Article.PlanarGeometry.height
        (fun j ψ => χ j (PlanarTransport.normal ψ)) v τ φ) θ) =
        fun τ => PlanarAmbientFrame.angularSlope χ (fun j => v j τ) (PlanarTransport.normal θ) :=
      funext fun τ => hS τ θ
    rw [heq, (hSt t ht θ).deriv]
    linarith
  · have heq : (fun ψ => deriv (fun φ => BfgsCoverage.Article.PlanarGeometry.height
        (fun j ψ => χ j (PlanarTransport.normal ψ)) v t φ) ψ) =
        fun ψ => PlanarAmbientFrame.angularSlope χ (fun j => v j t) (PlanarTransport.normal ψ) :=
      funext fun ψ => hS t ψ
    rw [heq, (hSθ t θ).deriv]
    linarith

open AffineCriticalObjective in
/-- Item `C/09_C/disp/018` (`companion/chapters/09_C.tex:205-208`), equation `C:eq:w`, the
precondition of the definition: "At a smooth point near $C$, write
$n(\theta(x))=\nabla F(x)/\norm{\nabla F(x)}$". Under the standing assumptions of §4, on a
neighborhood of $C$ every gradient is nonzero, so its unit normal has an angle $\theta(x)$. (The
formula itself is `PlanarGeometry.fieldFormula`, unfolded by `PlanarGeometry.field_eq_fieldFormula`.) -/
theorem smooth_point_normal_exists (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    ∀ᶠ x in 𝓝ˢ C, ∀ g : Vec 2, HasFDerivAt F (gradientFunctional g) x →
      g ≠ 0 ∧ ∃ θ : ℝ, PlanarTransport.normal θ = PlanarNormalGeometry.normalized g := by
  have hopen : IsOpen {x | Fstar < F x} := isOpen_lt continuous_const (convex_continuous hF)
  have hsub : C ⊆ {x | Fstar < F x} := fun x hx => by
    show Fstar < F x
    rw [hCℓ hx]
    exact hℓ
  filter_upwards [hopen.mem_nhdsSet.mpr hsub] with x hx g hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hmin := global_minimum_of_zero_gradient hF hg
    obtain ⟨⟨xs, hxs⟩, -⟩ := hFstar
    have := hmin xs
    rw [hxs] at this
    exact absurd hx (not_lt.mpr this)
  exact ⟨hg0, BfgsCoverage.Article.PlanarGeometry.exists_angle _
    (PlanarObjectiveField.normalized_sqNorm hg0)⟩

/-- Item `C/09_C/prose/045` (`companion/chapters/09_C.tex:209`), anchor "These expressions
are periodic in $\theta$".

For angular cutoffs $\theta\mapsto\chi_j(n(\theta))$ of differentiable ambient cutoffs: $h$ and
the formula $hn+h_\theta T$ of display `C/09_C/disp/018` are $2\pi$-periodic in $\theta$, and the
formula takes the same value at any two angles with the same unit normal, so no global choice of
angle is needed. -/
theorem field_formula_periodic {m : ℕ} (χ : Fin m → Vec 2 → ℝ)
    (hχ : ∀ j, Differentiable ℝ (χ j)) (v : Fin m → ℝ → Vec 2) (t : ℝ) :
    (∀ θ, BfgsCoverage.Article.PlanarGeometry.height (fun j φ => χ j (PlanarTransport.normal φ)) v t
        (θ + 2 * Real.pi) =
        BfgsCoverage.Article.PlanarGeometry.height (fun j φ => χ j (PlanarTransport.normal φ)) v t θ) ∧
      (∀ θ, BfgsCoverage.Article.PlanarGeometry.fieldFormula
          (fun j φ => χ j (PlanarTransport.normal φ)) v t (θ + 2 * Real.pi) =
        BfgsCoverage.Article.PlanarGeometry.fieldFormula
          (fun j φ => χ j (PlanarTransport.normal φ)) v t θ) ∧
      ∀ θ θ', PlanarTransport.normal θ = PlanarTransport.normal θ' →
        BfgsCoverage.Article.PlanarGeometry.fieldFormula
            (fun j φ => χ j (PlanarTransport.normal φ)) v t θ =
          BfgsCoverage.Article.PlanarGeometry.fieldFormula
            (fun j φ => χ j (PlanarTransport.normal φ)) v t θ' := by
  refine ⟨fun θ => PlanarJoinedFrame.height_periodic χ (fun j => v j t) θ,
    fun θ => BfgsCoverage.Article.PlanarGeometry.fieldFormula_periodic χ v t θ,
    fun θ θ' hθ => ?_⟩
  have h1 : BfgsCoverage.Article.PlanarGeometry.fieldFormula
      (fun j φ => χ j (PlanarTransport.normal φ)) v t θ =
      PlanarAmbientFrame.frame χ (fun j => v j t) (PlanarTransport.normal θ) := by
    rw [PlanarAmbientFrame.frame_eq_angular_frame _ hχ θ]
    rfl
  have h2 : BfgsCoverage.Article.PlanarGeometry.fieldFormula
      (fun j φ => χ j (PlanarTransport.normal φ)) v t θ' =
      PlanarAmbientFrame.frame χ (fun j => v j t) (PlanarTransport.normal θ') := by
    rw [PlanarAmbientFrame.frame_eq_angular_frame _ hχ θ']
    rfl
  rw [h1, h2, hθ]

open AffineCriticalObjective in
/-- Item `C/09_C/disp/019` (`companion/chapters/09_C.tex:212-214`), equation
`C:eq:nearcorner`, with the preceding sentence (line 211): "Where $\chi_j=1$, $h=n^Tv_j$ and
$h_\theta=T^Tv_j$, so
\[ w(x)=v_j(F(x)). \]"
Under the standing assumptions of §4, for angular cutoffs with disjoint supports, at a smooth
point $x$ (gradient $g$) with normal angle $\theta$ and $w(x)$ given by display
`C/09_C/disp/018`: if $\chi_j=1$ near $\theta$, then $h(F(x),\theta)=n(\theta)^Tv_j(F(x))$,
$h_\theta(F(x),\theta)=T(\theta)^Tv_j(F(x))$ and $w(x)=v_j(F(x))$. -/
theorem corner_formula (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    {m : ℕ} (χ : Fin m → ℝ → ℝ)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (w : Vec 2 → Vec 2) (x g : Vec 2)
    (_hg : HasFDerivAt F (gradientFunctional g) x) (θ : ℝ)
    (_hθ : PlanarTransport.normal θ = PlanarNormalGeometry.normalized g)
    (hw : w x = BfgsCoverage.Article.PlanarGeometry.fieldFormula χ v (F x) θ) (j : Fin m)
    (hplateau : ∀ᶠ φ in 𝓝 θ, χ j φ = 1) :
    BfgsCoverage.Article.PlanarGeometry.height χ v (F x) θ =
        dot (PlanarTransport.normal θ) (v j (F x)) ∧
      deriv (BfgsCoverage.Article.PlanarGeometry.height χ v (F x)) θ =
        dot (PlanarTransport.tangent θ) (v j (F x)) ∧ w x = v j (F x) := by
  have hsingle : ∀ φ, χ j φ = 1 → BfgsCoverage.Article.PlanarGeometry.height χ v (F x) φ =
      dot (PlanarTransport.normal φ) (v j (F x)) := by
    intro φ hφ
    have hother : ∀ i, i ≠ j → χ i φ = 0 := by
      intro i hij
      by_contra hne
      exact Set.disjoint_left.mp (hχsupp hij) hne (by rw [Function.mem_support, hφ]; norm_num)
    unfold BfgsCoverage.Article.PlanarGeometry.height
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hother i hij, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h), hφ]
    ring
  have hh := hsingle θ hplateau.self_of_nhds
  have hd : HasDerivAt (fun φ => dot (PlanarTransport.normal φ) (v j (F x)))
      (dot (PlanarTransport.tangent θ) (v j (F x))) θ := by
    have hc := (gradientFunctional (v j (F x))).hasFDerivAt.comp_hasDerivAt θ
      (PlanarTransport.normal_hasDerivAt θ)
    simpa only [gradientFunctional_apply, dot, mul_comm] using hc
  have hderiv : deriv (BfgsCoverage.Article.PlanarGeometry.height χ v (F x)) θ =
      dot (PlanarTransport.tangent θ) (v j (F x)) := by
    apply HasDerivAt.deriv
    apply hd.congr_of_eventuallyEq
    filter_upwards [hplateau] with φ hφ
    exact hsingle φ hφ
  refine ⟨hh, hderiv, ?_⟩
  rw [hw, BfgsCoverage.Article.PlanarGeometry.fieldFormula, hh, hderiv]
  exact PlanarTransport.reconstruct θ (v j (F x))

open AffineCriticalObjective PlanarNormalGeometry in
/-- Item `C/09_C/prose/046` (`companion/chapters/09_C.tex:215`), anchor "This holds on a
whole neighborhood of the corresponding switching curve".

"This holds on a whole neighborhood of the corresponding switching curve, on both sides. Define
$w$ by \eqref{C:eq:nearcorner} on the curve itself." Under the standing assumptions of §4, at a
nonsmooth point $c\in C$ with its two-branch data and curve $p$ (display `C/09_C/disp/014`), for
smooth ambient cutoffs with disjoint supports, $\chi_j=1$ on a neighborhood of the normal arc at
$c$, and $v_j=p'$: near $c$ every subgradient is nonzero with unit normal in the plateau of
$\chi_j$, and the field $w$ of the construction (`PlanarObjectiveField.field`, which is
\eqref{C:eq:w} at smooth points and $v_j(F)$ on the curve) satisfies $w(z)=v_j(F(z))$ for all $z$
near $c$, smooth or not (article `PlanarGeometry.corner_field`). -/
theorem corner_field_neighborhood (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t)
    {m : ℕ} (χ : Fin m → Vec 2 → ℝ)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (j : Fin m) (hvj : v j = deriv p)
    (hplateau : ∀ᶠ u in 𝓝ˢ (normalSector (coordinateGradient f₁ c)
      (coordinateGradient f₂ c)), χ j u = 1)
    (w : Vec 2 → Vec 2) (hw : w = PlanarObjectiveField.field hF χ v) :
    (∀ᶠ z in 𝓝 c, ∀ a ∈ ConvexSubdifferential.subdifferential F z, a ≠ 0 ∧
      ∀ᶠ u in 𝓝 (normalized a), χ j u = 1) ∧ ∀ᶠ z in 𝓝 c, w z = v j (F z) :=
  BfgsCoverage.Article.PlanarGeometry.corner_field F hF Fstar hFstar C ℓ ⟨c, hc⟩ hCcpt hCℓ hℓ
    hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) c hc hcns
    V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC hpdef χ hχsupp v j hvj hplateau
    w hw

open AffineCriticalObjective PlanarNormalGeometry ConvexSubdifferential in
/-- Item `C/09_C/prose/047` (`companion/chapters/09_C.tex:215`), anchor "The field thus
extends continuously and locally Lipschitzly".

In the setting of `corner_field_neighborhood`: the field is continuous at the corner $c$ and
Lipschitz on a neighborhood of $c$ ("across the gradient jump"). -/
theorem field_lipschitz_at_corner (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t)
    {m : ℕ} (χ : Fin m → Vec 2 → ℝ)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (j : Fin m) (hvj : v j = deriv p)
    (hplateau : ∀ᶠ u in 𝓝ˢ (normalSector (coordinateGradient f₁ c)
      (coordinateGradient f₂ c)), χ j u = 1)
    (w : Vec 2 → Vec 2) (hw : w = PlanarObjectiveField.field hF χ v) :
    ContinuousAt w c ∧ ∃ L : ℝ≥0, ∃ U ∈ 𝓝 c, LipschitzOnWith L w U := by
  obtain ⟨hpair, hC1⟩ := corner_velocity F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit
    hregular c hc hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC hpdef
    (deriv p) rfl
  have hcl : F c = ℓ := hCℓ hc
  set f : Fin 2 → Vec 2 → ℝ := ![f₁, f₂] with hfdef
  have hrep : LocalFiniteMax F f c := by
    filter_upwards [hV.mem_nhds hcV] with z hz
    exact BfgsCoverage.Article.PlanarGeometry.isGreatest_of_max f (hmax z hz)
  have hg : ∀ i, HasFDerivAt (f i) (gradientFunctional (coordinateGradient (f i) c)) c := by
    intro i
    fin_cases i
    · exact hasFDerivAt_coordinateGradient
        ((hC₁.contDiffAt (hV.mem_nhds hcV)).differentiableAt (by norm_num))
    · exact hasFDerivAt_coordinateGradient
        ((hC₂.contDiffAt (hV.mem_nhds hcV)).differentiableAt (by norm_num))
  have hact : ∀ i, f i c = F c := by
    intro i
    fin_cases i
    · exact hact₁
    · exact hact₂
  have hrate : ∀ i, dot (coordinateGradient (f i) c) (v j (F c)) = 1 := by
    have h := hpair.self_of_nhds
    rw [hpℓ] at h
    intro i
    rw [hvj, hcl]
    fin_cases i
    · exact h.1
    · exact h.2
  have hvC1 : ContDiffAt ℝ 1 (v j) (F c) := by rw [hvj, hcl]; exact hC1
  subst hw
  obtain ⟨L, U, hU, hLU⟩ := PlanarObjectiveField.field_lipschitz_near_corner hF hrep hg hact hrate
    v hχsupp hplateau hvC1
  exact ⟨(hLU.continuousOn.continuousAt hU), L, U, hU, hLU⟩

/-- Item `C/09_C/prose/048` (`companion/chapters/09_C.tex:215`), anchor "Away from the curves
it is $C^1$."

At a point $x$ where $F$ is $C^2$ with $\nabla F(x)\ne0$ (away from the switching curves), for
smooth ambient cutoffs and velocities $C^1$ at $F(x)$, the field
`PlanarObjectiveField.field hF χ v` is $C^1$ at $x$. -/
theorem field_C1_off_curves {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F) {m : ℕ}
    (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (v : Fin m → ℝ → Vec 2)
    (x : Vec 2) (hvx : ∀ j, ContDiffAt ℝ 1 (v j) (F x)) (hFx : ContDiffAt ℝ 2 F x)
    (hgx : coordinateGradient F x ≠ 0) :
    ContDiffAt ℝ 1 (PlanarObjectiveField.field hF χ v) x :=
  PlanarObjectiveField.field_contDiffAt_smooth hF hχ hvx hFx hgx

/-- Item `C/09_C/prose/049` (`companion/chapters/09_C.tex:215`), anchor "On a smaller compact
neighborhood of $C$, all close-pair Lipschitz and piecewise derivative bounds are uniform."

If the field $w$ is locally Lipschitz on an open $N\supseteq C$ ($C$ compact), then there are an
open $V\supseteq C$ and a compact $Q$ with $\overline V\subseteq Q\subseteq N$, and uniform
constants $M$, $\rho>0$, $G>0$: on every ball of radius $\rho$ about a point of $Q$ the field is
$M$-Lipschitz (close pairs), $\norm{w}\le G$ on $Q$, and $\norm{Dw}\le M$ wherever on $Q$ the
derivative exists (the operator norm of `fderiv`). -/
theorem uniform_buffer_bounds (C : Set (Vec 2)) (hC : IsCompact C) (w : Vec 2 → Vec 2)
    (N : Set (Vec 2)) (hN : IsOpen N) (hCN : C ⊆ N)
    (hLip : ∀ p ∈ N, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 p, LipschitzOnWith L w U) :
    ∃ V Q : Set (Vec 2), IsOpen V ∧ C ⊆ V ∧ closure V ⊆ Q ∧ IsCompact Q ∧ Q ⊆ N ∧
      ∃ (M : ℝ≥0) (ρ : ℝ), 0 < ρ ∧ ∃ G : ℝ, 0 < G ∧
        (∀ p ∈ Q, Metric.ball p ρ ⊆ N ∧ LipschitzOnWith M w (Metric.ball p ρ)) ∧
        (∀ p ∈ Q, sqNorm (w p) ≤ G ^ 2) ∧ ∀ p ∈ Q, ‖fderiv ℝ w p‖ ≤ M :=
  PlanarObjectiveField.exists_compact_uniform_field_buffer hC hN hCN hLip

open AffineCriticalObjective in
/-- Item `C/09_C/disp/020` (`companion/chapters/09_C.tex:218-220`), equation
`C:eq:visibility`: at smooth points
\[ \nabla F(x)^Tw(x)=\norm{\nabla F(x)}h(F(x),\theta(x))>0. \]
Under the standing assumptions of §4, with angular cutoffs $0\le\chi_j\le1$ with disjoint
supports chosen where $n^Tv_j>0$ (at the level $F(x)$), at a point $x$ with gradient $g\ne0$,
normal angle $\theta$ and $w(x)$ given by \eqref{C:eq:w}. -/
theorem visibility (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    {m : ℕ} (χ : Fin m → ℝ → ℝ) (hχ01 : ∀ j φ, χ j φ ∈ Icc (0 : ℝ) 1)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (w : Vec 2 → Vec 2) (x g : Vec 2)
    (_hg : HasFDerivAt F (gradientFunctional g) x) (hg0 : g ≠ 0)
    (θ : ℝ) (hθ : PlanarTransport.normal θ = PlanarNormalGeometry.normalized g)
    (hw : w x = BfgsCoverage.Article.PlanarGeometry.fieldFormula χ v (F x) θ)
    (hpos : ∀ j, χ j θ ≠ 0 → 0 < dot (PlanarTransport.normal θ) (v j (F x))) :
    dot g (w x) = ‖euclideanVector g‖ * BfgsCoverage.Article.PlanarGeometry.height χ v (F x) θ ∧
      0 < ‖euclideanVector g‖ * BfgsCoverage.Article.PlanarGeometry.height χ v (F x) θ := by
  have hgn : 0 < ‖euclideanVector g‖ := norm_pos_iff.mpr (by
    intro he
    exact hg0 (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) he))
  have hgeq : g = ‖euclideanVector g‖ • PlanarTransport.normal θ := by
    rw [hθ, PlanarNormalGeometry.normalized, smul_smul, mul_inv_cancel₀ hgn.ne', one_smul]
  have hpair : dot (PlanarTransport.normal θ) (w x) =
      BfgsCoverage.Article.PlanarGeometry.height χ v (F x) θ := by
    rw [hw]
    exact PlanarTransport.normal_pairing_angularFrame
      (BfgsCoverage.Article.PlanarGeometry.height χ v (F x))
      (deriv (BfgsCoverage.Article.PlanarGeometry.height χ v (F x))) θ
  have hheight : 0 < BfgsCoverage.Article.PlanarGeometry.height χ v (F x) θ := by
    by_cases he : ∃ i, χ i θ ≠ 0
    · obtain ⟨i, hi⟩ := he
      have hother : ∀ k, k ≠ i → χ k θ = 0 := by
        intro k hki
        by_contra hne
        exact Set.disjoint_left.mp (hχsupp hki) hne hi
      have heq : BfgsCoverage.Article.PlanarGeometry.height χ v (F x) θ =
          1 + χ i θ * (dot (PlanarTransport.normal θ) (v i (F x)) - 1) := by
        unfold BfgsCoverage.Article.PlanarGeometry.height
        rw [Finset.sum_eq_single i (fun k _ hki => by rw [hother k hki, zero_mul])
          (fun h => absurd (Finset.mem_univ i) h)]
      rw [heq]
      have hc := hχ01 i θ
      have hcpos : 0 < χ i θ := lt_of_le_of_ne hc.1 (fun h => hi h.symm)
      have hp := mul_pos hcpos (hpos i hi)
      nlinarith [hc.2]
    · push_neg at he
      simp only [BfgsCoverage.Article.PlanarGeometry.height, he, zero_mul, Finset.sum_const_zero,
        add_zero]
      norm_num
  refine ⟨?_, mul_pos hgn hheight⟩
  conv_lhs => rw [hgeq]
  change dotProduct (‖euclideanVector g‖ • PlanarTransport.normal θ) (w x) = _
  rw [smul_dotProduct]
  change ‖euclideanVector g‖ * dot (PlanarTransport.normal θ) (w x) = _
  rw [hpair]

open AffineCriticalObjective PlanarNormalGeometry ConvexSubdifferential in
/-- Item `C/09_C/prose/050` (`companion/chapters/09_C.tex:221`), anchor "At a switching
point, every subgradient has inner product one with $w$."

In the setting of `corner_field_neighborhood`, at every switching point $p_j(t)$ of the curve
with $t$ near $\ell$, every subgradient $a\in\partial F(p_j(t))$ satisfies $a^Tw(p_j(t))=1$. -/
theorem corner_unit_pairing (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c : Vec 2) (hc : c ∈ C) (hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (hf₁ : ConvexOn ℝ V f₁) (hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t)
    {m : ℕ} (χ : Fin m → Vec 2 → ℝ)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (j : Fin m) (hvj : v j = deriv p)
    (hplateau : ∀ᶠ u in 𝓝ˢ (normalSector (coordinateGradient f₁ c)
      (coordinateGradient f₂ c)), χ j u = 1)
    (w : Vec 2 → Vec 2) (hw : w = PlanarObjectiveField.field hF χ v) :
    ∀ᶠ t in 𝓝 ℓ, ∀ a ∈ subdifferential F (p t), dot a (w (p t)) = 1 := by
  obtain ⟨-, hweq⟩ := corner_field_neighborhood F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict
    hnoncrit hregular c hc hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC
    hpdef χ hχsupp v j hvj hplateau w hw
  have hpt : Tendsto p (𝓝 ℓ) (𝓝 c) := by
    simpa only [ContinuousAt, hpℓ] using hpC.continuousAt
  filter_upwards [hpt.eventually hweq, along_curve F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict
    hnoncrit hregular c hc hcns V hV hcV f₁ f₂ hf₁ hf₂ hC₁ hC₂ hmax hact₁ hact₂ hind p hpℓ hpC
    hpdef] with t hwt ⟨_, hrep, hg, hact, hFt, h1, h2⟩
  intro a ha
  rw [PlanarNormalGeometry.two_branch_subdifferential_eq_segment hF hrep hg hact] at ha
  obtain ⟨r, s, hr, hs, hrs, rfl⟩ := ha
  rw [hwt, hFt, hvj]
  change dotProduct (r • coordinateGradient f₁ (p t) + s • coordinateGradient f₂ (p t))
    (deriv p t) = 1
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
  change r * dot (coordinateGradient f₁ (p t)) (deriv p t) +
    s * dot (coordinateGradient f₂ (p t)) (deriv p t) = 1
  rw [h1, h2]
  linarith

open AffineCriticalObjective in
/-- Item `C/09_C/disp/021` (`companion/chapters/09_C.tex:229-231`), equation
`C:eq:angleidentity`: "At fixed $t$, differentiation gives the exact identity
\[ \partial_\theta(hn+h_\theta T)=(h+h_{\theta\theta})T." \]
Under the standing assumptions of §4, for $C^2$ angular cutoffs, any velocities and any level
$t$, with $h=h(t,\cdot)$ of display `C/09_C/disp/017` (the variable `h` with its definition), at
every angle $\theta$. No sign or convexity condition on $h$ is used. -/
theorem angle_identity (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    {m : ℕ} (χ : Fin m → ℝ → ℝ) (hχ : ∀ j, ContDiff ℝ 2 (χ j))
    (v : Fin m → ℝ → Vec 2) (t : ℝ) (h : ℝ → ℝ)
    (hh : h = BfgsCoverage.Article.PlanarGeometry.height χ v t) (θ : ℝ) :
    HasDerivAt (fun φ => h φ • PlanarTransport.normal φ + deriv h φ • PlanarTransport.tangent φ)
      ((h θ + deriv (deriv h) θ) • PlanarTransport.tangent θ) θ := by
  have hC : ContDiff ℝ 2 h := hh ▸ BfgsCoverage.Article.PlanarGeometry.height_contDiff χ hχ v t
  have hC' : ContDiff ℝ (1 + 1) h := by simpa using hC
  obtain ⟨hdiff, -, hderiv⟩ := contDiff_succ_iff_deriv.mp hC'
  have h1 : HasDerivAt h (deriv h θ) θ := (hdiff θ).hasDerivAt
  have h2 : HasDerivAt (deriv h) (deriv (deriv h) θ) θ :=
    ((hderiv.differentiable le_rfl) θ).hasDerivAt
  exact PlanarTransport.angularFrame_hasDerivAt h (deriv h) θ (deriv h θ) (deriv (deriv h) θ)
    h1 h2 rfl

open AffineCriticalObjective in
/-- Item `C/09_C/disp/022` (`companion/chapters/09_C.tex:233-235`), equation
`C:eq:triangular`, and Item `C/09_C/prose/052` (`companion/chapters/09_C.tex:232`), anchor
"Therefore, at a smooth point, $Dw(x)$ maps the one-dimensional tangent line".

Under the standing assumptions of §4, with smooth ambient cutoffs, at a point $x$ where $F$ is
$C^2$ with $\nabla F(x)\ne0$, velocities $C^1$ at $F(x)$, and $w$ given by \eqref{C:eq:w} near
$x$ (at every angle of the normal): $w$ is differentiable at $x$, $Dw(x)$ maps the tangent line
$\{u:n^Tu=0\}$ of the level curve into itself, and with $n=\nabla F(x)/\norm{\nabla F(x)}$,
$T$ the rotated normal, $a=T^TDwT$, $b=T^TDw\,n$, $e=n^TDw\,n$: $Dw\,T=aT$ and
$Dw\,n=bT+en$, i.e. in the orthonormal basis $(T,n)$
\[ Dw=\begin{pmatrix}a&b\\0&e\end{pmatrix}. \] -/
theorem triangular_derivative (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (v : Fin m → ℝ → Vec 2)
    (w : Vec 2 → Vec 2) (x : Vec 2) (hFx : ContDiffAt ℝ 2 F x)
    (hgx : coordinateGradient F x ≠ 0) (hvx : ∀ j, ContDiffAt ℝ 1 (v j) (F x))
    (hw : ∀ᶠ z in 𝓝 x, ∀ θ, PlanarTransport.normal θ =
        PlanarNormalGeometry.normalized (coordinateGradient F z) →
        w z = BfgsCoverage.Article.PlanarGeometry.fieldFormula
          (fun j φ => χ j (PlanarTransport.normal φ)) v (F z) θ)
    (n T : Vec 2) (hn : n = PlanarNormalGeometry.normalized (coordinateGradient F x))
    (hT : T = PlanarAmbientFrame.rotate n) (a b e : ℝ) (ha : a = dot T (fderiv ℝ w x T))
    (hb : b = dot T (fderiv ℝ w x n)) (he : e = dot n (fderiv ℝ w x n)) :
    DifferentiableAt ℝ w x ∧ (∀ u, dot n u = 0 → dot n (fderiv ℝ w x u) = 0) ∧
      fderiv ℝ w x T = a • T ∧ fderiv ℝ w x n = b • T + e • n :=
  BfgsCoverage.Article.PlanarGeometry.field_derivative_triangular hF χ hχ v w x hFx hgx hvx hw n T
    hn hT a b e ha hb he

open AffineCriticalObjective in
/-- Item `C/09_C/prose/054` (`companion/chapters/09_C.tex:236`), anchor "The coefficients are
bounded in the compact neighborhood."

Under the standing assumptions of §4, if $w$ is locally Lipschitz on an open $N$ containing the
compact neighborhood $Q$, there is one bound $B$ for the coefficients $a=T^TDwT$, $b=T^TDw\,n$,
$e=n^TDw\,n$ at every $x\in Q$ and every unit normal $n$ with $T$ its rotation. -/
theorem coefficients_bounded (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (w : Vec 2 → Vec 2) (Q N : Set (Vec 2)) (hQ : IsCompact Q) (hN : IsOpen N) (hQN : Q ⊆ N)
    (hLip : ∀ p ∈ N, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 p, LipschitzOnWith K w V) :
    ∃ B : ℝ, ∀ x ∈ Q, ∀ n : Vec 2, sqNorm n = 1 →
      |dot (PlanarAmbientFrame.rotate n) (fderiv ℝ w x (PlanarAmbientFrame.rotate n))| ≤ B ∧
        |dot (PlanarAmbientFrame.rotate n) (fderiv ℝ w x n)| ≤ B ∧
        |dot n (fderiv ℝ w x n)| ≤ B := by
  have hLoc : LocallyLipschitzOn N w := by
    intro p hp
    obtain ⟨K, V, hV, hKV⟩ := hLip p hp
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hKV⟩
  obtain ⟨M, ρ, hρ, hballs⟩ :=
    CenteredSmoothSublinear.compact_uniform_local_lipschitz hN hQ hQN hLoc
  refine ⟨2 * M, ?_⟩
  intro x hx n hn
  have hM : ‖fderiv ℝ w x‖ ≤ M :=
    norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds x hρ) (hballs x hx).2
  have hrot : sqNorm (PlanarAmbientFrame.rotate n) = 1 :=
    (PlanarObjectiveField.rotate_sqNorm n).trans hn
  refine ⟨?_, ?_, ?_⟩
  · exact (PlanarObjectiveField.abs_dot_unit_map_le hrot hrot _).trans (by gcongr)
  · exact (PlanarObjectiveField.abs_dot_unit_map_le hrot hn _).trans (by gcongr)
  · exact (PlanarObjectiveField.abs_dot_unit_map_le hn hn _).trans (by gcongr)

/-! ### §5. Three endpoint estimates (lines 246-329) -/

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/prose/057` (`companion/chapters/09_C.tex:247`), anchor "For each fixed
valid pair $(c_1,c_2)$, the following three estimates".

Under the standing assumptions of §§4-5, for each valid pair $0<c_1<c_2<1$, one
objective-constructed field $w$ (`PlanarObjectiveField.field hF χ v` for smooth ambient cutoffs
$\chi_j$ and velocities $v_j$) satisfies the three estimates of Lemmas `C:lem:trans`,
`C:lem:transport` and `C:lem:secant` simultaneously. There are an open $U\supseteq C$, a compact
buffer $Q\supseteq\overline U$, and uniform distance and visibility constants $\delta,\eta>0$:
$w$ is locally Lipschitz on an open $N\supseteq Q$ and bounded on $Q$; every subgradient at a
point $p\in Q$ has the same pairing with $w(p)$, at least $\eta$; every eligible pair $x,z\in U$
with $\norm{s}<\delta$ (Euclidean; $s=z-x$) has its whole segment in $Q$, and for such pairs:
$|\det(s,w(x+\theta s))|\ge\kappa\norm{s}$ ($0\le\theta\le1$); $w(z)=\lambda w(x)+\beta s$ with
$\lambda>0$, $|\log\lambda|\le C_td$ and $\lambda^2\le1+C'd$ when $d\le d_0$; and
$(y^Tw(z))^2/t\le C_0$, where $g,h$ are the gradients at $x,z$, $y=h-g$, $d=-g^Ts$, $t=y^Ts$.
All constants, neighborhoods and the field are chosen before the pair (quantifier order), and no
BFGS matrix or run appears. -/
theorem three_estimates (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ (m : ℕ) (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2) (U Q : Set (Vec 2))
      (w : Vec 2 → Vec 2) (η δ : ℝ),
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ w = PlanarObjectiveField.field hF χ v ∧
      IsOpen U ∧ C ⊆ U ∧ IsCompact Q ∧ closure U ⊆ Q ∧ 0 < η ∧ 0 < δ ∧
      (∃ N : Set (Vec 2), IsOpen N ∧ Q ⊆ N ∧
        ∀ p ∈ N, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 p, LipschitzOnWith K w V) ∧
      (∃ B : ℝ, ∀ p ∈ Q, ‖euclideanVector (w p)‖ ≤ B) ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, η ≤ dot g (w p)) ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, ∀ g' ∈ subdifferential F p,
        dot g (w p) = dot g' (w p)) ∧
      (∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
        ‖euclideanVector (z - x)‖ < δ → ∀ θ ∈ Icc (0 : ℝ) 1, x + θ • (z - x) ∈ Q) ∧
      (∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
        ‖euclideanVector (z - x)‖ < δ → ∀ θ ∈ Icc (0 : ℝ) 1,
          κ * ‖euclideanVector (z - x)‖ ≤ |pairDet (z - x) (w (x + θ • (z - x)))|) ∧
      (∃ Ct C' d₀ : ℝ, 0 ≤ Ct ∧ 0 ≤ C' ∧ 0 < d₀ ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2,
        EligiblePair F c₁ c₂ x z g h → ‖euclideanVector (z - x)‖ < δ →
        ∃ lam β : ℝ, 0 < lam ∧ w z = lam • w x + β • (z - x) ∧
          |Real.log lam| ≤ Ct * (-dot g (z - x)) ∧
          (-dot g (z - x) ≤ d₀ → lam ^ 2 ≤ 1 + C' * (-dot g (z - x)))) ∧
      (∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
        ‖euclideanVector (z - x)‖ < δ → (dot (h - g) (w z)) ^ 2 / dot (h - g) (z - x) ≤ C₀) := by
  obtain ⟨m, χ, v, hχ, U, Q, hU, hCU, hUQ, hQ, η, κ, δ, C₁, L, C₀, hη, hκ, hδ, hC₁, hL, hC₀,
    hLip, hvis, hcommon, hpairs⟩ :=
    PlanarAllPairs.source_all_endpoint_estimates hF hCcpt (fun x hx => hCℓ hx) hstrict
      (fun p hp => BfgsCoverage.Article.PlanarGeometry.regularity_of_literal (hregular p hp))
      hnoncrit hc₁ hc₂
  obtain ⟨N, hN, hQN, hLipN⟩ := PlanarObjectiveField.exists_open_local_lipschitz_extension hLip
  have hcont : ContinuousOn (fun p => euclideanVector (PlanarObjectiveField.field hF χ v p)) Q := by
    intro p hp
    obtain ⟨K, V, hV, hKV⟩ := hLip p hp
    exact ((PiLp.continuous_equiv_symm _ _).continuousAt.comp
      (hKV.continuousOn.continuousAt hV)).continuousWithinAt
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hcont
  refine ⟨m, χ, v, U, Q, PlanarObjectiveField.field hF χ v, η, δ, hχ, rfl, hU, hCU, hQ, hUQ, hη,
    hδ, ⟨N, hN, hQN, hLipN⟩, ⟨B, hB⟩, hvis, hcommon,
    fun x hx z hz g h hp hs θ hθ => ((hpairs x hx z hz g h hp hs).1 θ hθ).1,
    ⟨κ, hκ, fun x hx z hz g h hp hs θ hθ => ((hpairs x hx z hz g h hp hs).1 θ hθ).2⟩,
    ⟨C₁, L, 1, hC₁, hL, one_pos, fun x hx z hz g h hp hs => (hpairs x hx z hz g h hp hs).2.2⟩,
    ⟨C₀, hC₀, fun x hx z hz g h hp hs => (hpairs x hx z hz g h hp hs).2.1⟩⟩

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/prose/051` (`companion/chapters/09_C.tex:221`), anchor "Compactness on a
positive level neighborhood gives a uniform positive lower bound".

Under the standing assumptions of §4, the field of the construction has, on a compact
neighborhood $Q$ of $C$ ($C\subseteq U\subseteq Q$, $U$ open), a uniform positive lower bound
$\eta$ for the pairing \eqref{C:eq:visibility} with every subgradient, and a uniform bound $B$. -/
theorem uniform_visibility (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    ∃ (m : ℕ) (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2) (U Q : Set (Vec 2)) (η B : ℝ),
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ IsOpen U ∧ C ⊆ U ∧ U ⊆ Q ∧ IsCompact Q ∧ 0 < η ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, η ≤ dot g (PlanarObjectiveField.field hF χ v p)) ∧
      ∀ p ∈ Q, ‖euclideanVector (PlanarObjectiveField.field hF χ v p)‖ ≤ B := by
  obtain ⟨m, χ, v, U, Q, w, η, δ, hχ, hw, hU, hCU, hQ, hUQ, hη, -, -, ⟨B, hB⟩, hvis, -⟩ :=
    three_estimates F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit hregular (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  subst hw
  exact ⟨m, χ, v, U, Q, η, B, hχ, hU, hCU, subset_closure.trans hUQ, hQ, hη, hvis, hB⟩

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/lemma/C:lem:trans` (`companion/chapters/09_C.tex:249-256`), Lemma `C:lem:trans`
("Uniform transversality"), with its display `C/09_C/disp/023` (lines 251-254).

Under the standing assumptions of §§4-5 and for valid $0<c_1<c_2<1$: for the objective-constructed
field $w$ with the neighborhoods $U\subseteq Q$ and the uniform constants of §5 (as in
`three_estimates`), there is $\kappa>0$ such that
\[ |\det(s,w(x+\theta s))|\ge\kappa\norm{s}\quad(0\le\theta\le1) \]
for all sufficiently close ($\norm{s}<\delta$) eligible pairs $x,z\in U$, $s=z-x$
(`pairDet a b` $=a_1b_2-a_2b_1$). -/
theorem transversality (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ (m : ℕ) (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2) (U Q : Set (Vec 2))
      (w : Vec 2 → Vec 2) (η δ : ℝ),
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ w = PlanarObjectiveField.field hF χ v ∧
      IsOpen U ∧ C ⊆ U ∧ IsCompact Q ∧ closure U ⊆ Q ∧ 0 < η ∧ 0 < δ ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, η ≤ dot g (w p)) ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, ∀ g' ∈ subdifferential F p,
        dot g (w p) = dot g' (w p)) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
        ‖euclideanVector (z - x)‖ < δ → ∀ θ ∈ Icc (0 : ℝ) 1,
          κ * ‖euclideanVector (z - x)‖ ≤ |pairDet (z - x) (w (x + θ • (z - x)))| := by
  obtain ⟨m, χ, v, U, Q, w, η, δ, hχ, hw, hU, hCU, hQ, hUQ, hη, hδ, -, -, hvis, hcommon, -, htr,
    -, -⟩ := three_estimates F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit hregular c₁ c₂
      hc₁ hc₁₂ hc₂
  exact ⟨m, χ, v, U, Q, w, η, δ, hχ, hw, hU, hCU, hQ, hUQ, hη, hδ, hvis, hcommon, htr⟩

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/lemma/C:lem:transport` (`companion/chapters/09_C.tex:265-272`), Lemma
`C:lem:transport` ("Transport is charged to objective decrease"), with its display
`C/09_C/disp/025` (`C:eq:transport`, lines 267-270).

In the setting of Lemma `C:lem:trans`, for the same pairs there are scalars $\lambda>0$, $\beta$
with
\[ w(z)=\lambda w(x)+\beta s,\qquad |\log\lambda|\le Cd, \]
with one constant $C$ for all pairs ($d=-g^Ts$); in particular $\lambda^2\le1+C'd$ for
sufficiently small $d$: one $C'$ and one threshold $d_0>0$ (in fact $d_0=1$), chosen before the
pair. -/
theorem transport (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ (m : ℕ) (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2) (U Q : Set (Vec 2))
      (w : Vec 2 → Vec 2) (η δ : ℝ),
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ w = PlanarObjectiveField.field hF χ v ∧
      IsOpen U ∧ C ⊆ U ∧ IsCompact Q ∧ closure U ⊆ Q ∧ 0 < η ∧ 0 < δ ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, η ≤ dot g (w p)) ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, ∀ g' ∈ subdifferential F p,
        dot g (w p) = dot g' (w p)) ∧
      ∃ Ct C' d₀ : ℝ, 0 ≤ Ct ∧ 0 ≤ C' ∧ 0 < d₀ ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2,
        EligiblePair F c₁ c₂ x z g h → ‖euclideanVector (z - x)‖ < δ →
        ∃ lam β : ℝ, 0 < lam ∧ w z = lam • w x + β • (z - x) ∧
          |Real.log lam| ≤ Ct * (-dot g (z - x)) ∧
          (-dot g (z - x) ≤ d₀ → lam ^ 2 ≤ 1 + C' * (-dot g (z - x))) := by
  obtain ⟨m, χ, v, U, Q, w, η, δ, hχ, hw, hU, hCU, hQ, hUQ, hη, hδ, -, -, hvis, hcommon, -, -,
    htrans, -⟩ := three_estimates F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit hregular c₁
      c₂ hc₁ hc₁₂ hc₂
  exact ⟨m, χ, v, U, Q, w, η, δ, hχ, hw, hU, hCU, hQ, hUQ, hη, hδ, hvis, hcommon, htrans⟩

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/lemma/C:lem:secant` (`companion/chapters/09_C.tex:299-305`), Lemma
`C:lem:secant` ("Bounded secant correction"), with its display `C/09_C/disp/030`
(lines 301-303).

In the setting of Lemma `C:lem:trans`, there is a uniform $C_0<\infty$ such that
\[ \frac{(y^Tw(z))^2}{t}\le C_0 \]
for all sufficiently close eligible pairs in the same neighborhood ($y=h-g$, $t=y^Ts>0$). -/
theorem secant (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (hℓ : Fstar < ℓ)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ (m : ℕ) (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2) (U Q : Set (Vec 2))
      (w : Vec 2 → Vec 2) (η δ : ℝ),
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ w = PlanarObjectiveField.field hF χ v ∧
      IsOpen U ∧ C ⊆ U ∧ IsCompact Q ∧ closure U ⊆ Q ∧ 0 < η ∧ 0 < δ ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, η ≤ dot g (w p)) ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, ∀ g' ∈ subdifferential F p,
        dot g (w p) = dot g' (w p)) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
        ‖euclideanVector (z - x)‖ < δ → (dot (h - g) (w z)) ^ 2 / dot (h - g) (z - x) ≤ C₀ := by
  obtain ⟨m, χ, v, U, Q, w, η, δ, hχ, hw, hU, hCU, hQ, hUQ, hη, hδ, -, -, hvis, hcommon, -, -, -,
    hsec⟩ := three_estimates F hF Fstar hFstar C ℓ hCcpt hCℓ hℓ hstrict hnoncrit hregular c₁ c₂
      hc₁ hc₁₂ hc₂
  exact ⟨m, χ, v, U, Q, w, η, δ, hχ, hw, hU, hCU, hQ, hUQ, hη, hδ, hvis, hcommon, hsec⟩

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/disp/024` (`companion/chapters/09_C.tex:259-261`), in the proof of Lemma
`C:lem:trans`: "Descent selects $e=-w(p)/\norm{w(p)}$, so $d/\norm{s}\to-a^Te>0$. But
\[ t/\norm{s}\to(b-a)^Te=0." \]
Under the standing assumptions of §§4-5 and the facts established before (visibility $\eta>0$ and
the common pairing of $w$ on the compact neighborhood $Q$): pairs $x_k,z_k$ with gradients
$g_k,h_k$ coalesce to $p\in Q$, the unit steps $s_k/\norm{s_k}$ tend to $e$, the gradients tend
to the subgradient limits $a,b\in\partial F(p)$, and $e=-w(p)/\norm{w(p)}$; $d_k=-g_k^Ts_k$,
$t_k=(h_k-g_k)^Ts_k$. The display is a step of a proof by contradiction; it does not use
eligibility (with eligibility these assumptions are contradictory, which is the next sentence
of the proof), so eligibility is not assumed here. -/
theorem transversality_limit (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (w : Vec 2 → Vec 2) (Q : Set (Vec 2)) (η : ℝ) (hη : 0 < η)
    (hvis : ∀ p ∈ Q, ∀ a ∈ subdifferential F p, η ≤ dot a (w p))
    (hcommon : ∀ p ∈ Q, ∀ a ∈ subdifferential F p, ∀ b ∈ subdifferential F p,
      dot a (w p) = dot b (w p))
    (x z g h : ℕ → Vec 2) (_hs0 : ∀ k, z k - x k ≠ 0)
    (_hscoal : Tendsto (fun k => z k - x k) atTop (𝓝 0))
    (p : Vec 2) (hpQ : p ∈ Q) (_hxp : Tendsto x atTop (𝓝 p))
    (e a b : Vec 2)
    (he : Tendsto (fun k => PlanarNormalGeometry.normalized (z k - x k)) atTop (𝓝 e))
    (ha : Tendsto g atTop (𝓝 a)) (hb : Tendsto h atTop (𝓝 b))
    (hamem : a ∈ subdifferential F p) (hbmem : b ∈ subdifferential F p)
    (he_eq : e = -PlanarNormalGeometry.normalized (w p))
    (d t : ℕ → ℝ) (hd : ∀ k, d k = -dot (g k) (z k - x k))
    (ht : ∀ k, t k = dot (h k - g k) (z k - x k)) :
    Tendsto (fun k => d k / ‖euclideanVector (z k - x k)‖) atTop (𝓝 (-dot a e)) ∧
      0 < -dot a e ∧
      Tendsto (fun k => t k / ‖euclideanVector (z k - x k)‖) atTop (𝓝 (dot (b - a) e)) ∧
      dot (b - a) e = 0 := by
  have hdk : (fun k => d k / ‖euclideanVector (z k - x k)‖) =
      fun k => -dot (g k) (PlanarNormalGeometry.normalized (z k - x k)) := by
    funext k
    rw [hd k, BfgsCoverage.Article.PlanarGeometry.dot_normalized_right, neg_div]
  have htk : (fun k => t k / ‖euclideanVector (z k - x k)‖) =
      fun k => dot (h k - g k) (PlanarNormalGeometry.normalized (z k - x k)) := by
    funext k
    rw [ht k, BfgsCoverage.Article.PlanarGeometry.dot_normalized_right]
  have hwp : 0 < dot a (w p) := hη.trans_le (hvis p hpQ a hamem)
  have hw0 : w p ≠ 0 := by
    intro h0
    rw [h0] at hwp
    simp [dot] at hwp
  have hwn : 0 < ‖euclideanVector (w p)‖ := norm_pos_iff.mpr (by
    intro hz
    exact hw0 (congrArg (fun y : EuclideanSpace ℝ (Fin 2) => fun i => y i) hz))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdk]
    exact ((continuous_dot.tendsto _).comp (ha.prodMk_nhds he)).neg
  · rw [he_eq, BfgsCoverage.Article.PlanarGeometry.dot_neg_right_vec, neg_neg,
      BfgsCoverage.Article.PlanarGeometry.dot_normalized_right]
    exact div_pos hwp hwn
  · rw [htk]
    exact (continuous_dot.tendsto _).comp ((hb.sub ha).prodMk_nhds he)
  · rw [he_eq, BfgsCoverage.Article.PlanarGeometry.dot_neg_right_vec,
      BfgsCoverage.Article.PlanarGeometry.dot_normalized_right, dot_sub_left,
      hcommon p hpQ b hbmem a hamem, sub_self, zero_div, neg_zero]

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/disp/026` (`companion/chapters/09_C.tex:277-279`), in the proof of Lemma
`C:lem:transport`: "On a smooth part of the segment, use \eqref{C:eq:triangular}. The ordered
orthonormal basis $(T,n)$ has determinant $-1$. Consequently, with $s=s_TT+s_nn$, the correctly
oriented identity is
\[ \det(s,Dw\,s)=s_n[(a-e)s_T+bs_n]." \]
Under the standing assumptions of §§4-5, for an eligible pair with $s=z-x$ and a segment point
$q=x+\theta s$ where $F$ is $C^2$ with $\nabla F(q)\ne0$, velocities $C^1$ at $F(q)$ and $w$
given by \eqref{C:eq:w} near $q$, with $n,T,a,b,e$ as in `triangular_derivative` at $q$ and
$s_T=T^Ts$, $s_n=n^Ts$ (`pairDet u v` $=u_1v_2-u_2v_1$ is the determinant with columns
$u,v$). -/
theorem determinant_identity (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (v : Fin m → ℝ → Vec 2)
    (w : Vec 2 → Vec 2) (x z g h : Vec 2) (_hpair : EligiblePair F c₁ c₂ x z g h)
    (s : Vec 2) (_hs : s = z - x) (θ : ℝ) (_hθ : θ ∈ Icc (0 : ℝ) 1) (q : Vec 2)
    (_hq : q = x + θ • s) (hFq : ContDiffAt ℝ 2 F q)
    (hgq : coordinateGradient F q ≠ 0) (hvq : ∀ j, ContDiffAt ℝ 1 (v j) (F q))
    (hw : ∀ᶠ y in 𝓝 q, ∀ φ, PlanarTransport.normal φ =
        PlanarNormalGeometry.normalized (coordinateGradient F y) →
        w y = BfgsCoverage.Article.PlanarGeometry.fieldFormula
          (fun j ψ => χ j (PlanarTransport.normal ψ)) v (F y) φ)
    (n T : Vec 2) (hn : n = PlanarNormalGeometry.normalized (coordinateGradient F q))
    (hT : T = PlanarAmbientFrame.rotate n) (a b e : ℝ) (ha : a = dot T (fderiv ℝ w q T))
    (hb : b = dot T (fderiv ℝ w q n)) (he : e = dot n (fderiv ℝ w q n))
    (sT sn : ℝ) (hsT : sT = dot T s) (hsn : sn = dot n s) :
    pairDet T n = -1 ∧ s = sT • T + sn • n ∧
      pairDet s (fderiv ℝ w q s) = sn * ((a - e) * sT + b * sn) := by
  obtain ⟨-, htan, -, -⟩ := BfgsCoverage.Article.PlanarGeometry.field_derivative_triangular hF χ hχ
    v w q hFq hgq hvq hw n T hn hT a b e ha hb he
  have hunit : sqNorm n = 1 := hn ▸ PlanarObjectiveField.normalized_sqNorm hgq
  have hnT : dot n (fderiv ℝ w q T) = 0 :=
    htan T (hT ▸ PlanarAmbientFrame.rotate_orthogonal n)
  refine ⟨?_, ?_, ?_⟩
  · rw [hT]
    simp only [sqNorm, Fin.sum_univ_two] at hunit
    simp only [pairDet, PlanarAmbientFrame.rotate, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    nlinarith
  · have hrec := PlanarAmbientFrame.reconstruct hunit s
    rw [← hT, ← hsT, ← hsn] at hrec
    rw [← hrec, add_comm]
  · have hdet := PlanarObjectiveField.actual_tangent_map_determinant hunit (fderiv ℝ w q)
      (hT ▸ hnT) s
    rw [hdet, ← hT, ← ha, ← hb, ← he, ← hsT, ← hsn]

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/disp/027` (`companion/chapters/09_C.tex:281-284`), in the proof of Lemma
`C:lem:transport`: "We obtain, for one $C\ge0$,
\[ \left|\frac{D'_+(\theta)}{D(\theta)}\right|\le C|\varphi'_+(\theta)|,\qquad 0\le\theta<1." \]
Under the standing assumptions of §§4-5 and the facts established before: $w$ is the field of the
construction (smooth ambient cutoffs $\chi_j$, velocities $v_j$), locally Lipschitz on an open
$N\supseteq Q$ ($Q$ compact); at every point of $Q$ the velocities are $C^1$ at the level and the
point is smooth ($C^2$) or has $w=v_j\circ F$ nearby (a corner neighborhood); visibility
$g^Tw\ge\eta>0$ on $Q$; eligible pairs in $U$ with $\norm{s}<\delta$ have their segments in $Q$
and $|D(\theta)|\ge\kappa\norm{s}$ (Lemma `C:lem:trans`). Then one $C\ge0$, chosen before the
pair, works for every such pair, with $q(\theta)=x+\theta s$, $\varphi(\theta)=F(q(\theta))$,
$D(\theta)=\det(s,w(q(\theta)))$: $D$ has the right derivative $D'_+(\theta)$
(`derivWithin D (Ioi θ) θ`, a `HasDerivWithinAt` on `Ici θ`) and the display holds, with
$\varphi'_+(\theta)$ = `derivWithin φ (Ioi θ) θ`. -/
theorem determinant_quotient_bound (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (v : Fin m → ℝ → Vec 2)
    (w : Vec 2 → Vec 2) (hw : w = PlanarObjectiveField.field hF χ v)
    (U Q N : Set (Vec 2)) (hQ : IsCompact Q) (hN : IsOpen N) (hQN : Q ⊆ N)
    (hLip : ∀ p ∈ N, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 p, LipschitzOnWith K w V)
    (hv : ∀ p ∈ Q, ∀ j, ContDiffAt ℝ 1 (v j) (F p))
    (hstruct : ∀ p ∈ Q, ContDiffAt ℝ 2 F p ∨ ∃ j, ∀ᶠ y in 𝓝 p, w y = v j (F y))
    (η : ℝ) (hη : 0 < η) (hvis : ∀ p ∈ Q, ∀ a ∈ subdifferential F p, η ≤ dot a (w p))
    (κ δ : ℝ) (hκ : 0 < κ) (_hδ : 0 < δ)
    (hseg : ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
      ‖euclideanVector (z - x)‖ < δ → ∀ θ ∈ Icc (0 : ℝ) 1, x + θ • (z - x) ∈ Q ∧
        κ * ‖euclideanVector (z - x)‖ ≤ |pairDet (z - x) (w (x + θ • (z - x)))|) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
      ‖euclideanVector (z - x)‖ < δ →
      ∀ (s : Vec 2) (q : ℝ → Vec 2) (φ D : ℝ → ℝ), s = z - x →
        q = (fun θ => x + θ • s) → φ = (fun θ => F (q θ)) →
        D = (fun θ => pairDet s (w (q θ))) →
        ∀ θ ∈ Ico (0 : ℝ) 1,
          HasDerivWithinAt D (derivWithin D (Ioi θ) θ) (Ici θ) θ ∧
          |derivWithin D (Ioi θ) θ / D θ| ≤ Cq * |derivWithin φ (Ioi θ) θ| := by
  subst hw
  have hLoc : LocallyLipschitzOn N (PlanarObjectiveField.field hF χ v) := by
    intro p hp
    obtain ⟨K, V, hV, hKV⟩ := hLip p hp
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hKV⟩
  obtain ⟨M, ρ, hρ, hballs⟩ :=
    CenteredSmoothSublinear.compact_uniform_local_lipschitz hN hQ hQN hLoc
  have hM : ∀ p ∈ Q, ‖fderiv ℝ (PlanarObjectiveField.field hF χ v) p‖ ≤ M := fun p hp =>
    norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds p hρ) (hballs p hp).2
  have hc : ContinuousOn (fun p => sqNorm (PlanarObjectiveField.field hF χ v p)) Q :=
    continuous_sqNorm.comp_continuousOn (hLoc.continuousOn.mono hQN)
  obtain ⟨B, hB⟩ := hQ.bddAbove_image hc
  set G := Real.sqrt (|B| + 1) with hGdef
  have hG : 0 < G := Real.sqrt_pos.mpr (by positivity)
  have hW : ∀ p ∈ Q, sqNorm (PlanarObjectiveField.field hF χ v p) ≤ G ^ 2 := by
    intro p hp
    rw [hGdef, Real.sq_sqrt (by positivity : 0 ≤ |B| + 1)]
    exact (hB ⟨p, hp, rfl⟩).trans (by linarith [le_abs_self B])
  obtain ⟨Av, _hAv, hvel⟩ :=
    PlanarObjectiveField.compact_velocity_derivative_bound (convex_continuous hF) hQ hv
  have hμ : 0 < η / G := div_pos hη hG
  have hMn : 0 ≤ (M : ℝ) := M.coe_nonneg
  set A := max (6 * (M : ℝ) / (κ * (η / G))) (Av / κ) with hAdef
  have hA : 0 ≤ A := le_max_of_le_left (by positivity)
  refine ⟨A, hA, ?_⟩
  intro x hx z hz g h hp hs s q φ D hs_eq hq_eq hφ_eq hD_eq θ hθ
  subst hs_eq hq_eq hφ_eq hD_eq
  have hs0 : z - x ≠ 0 := PlanarAllPairs.eligible_step_ne_zero hp
  obtain ⟨hqQ, htr⟩ := hseg x hx z hz g h hp hs θ (Ico_subset_Icc_self hθ)
  have hφc : ConvexOn ℝ univ (fun τ : ℝ => F (x + τ • (z - x))) := by
    have hc := hF.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x + (z - x)))
    simpa only [AffineMap.lineMap_apply_module', add_sub_cancel_left, Function.comp_def,
      Set.preimage_univ, add_comm] using hc
  have hφr : HasDerivWithinAt (fun τ : ℝ => F (x + τ • (z - x)))
      (derivWithin (fun τ : ℝ => F (x + τ • (z - x))) (Ioi θ) θ) (Ici θ) θ :=
    (hφc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)).Ici_of_Ioi
  have hglower : DifferentiableAt ℝ F (x + θ • (z - x)) →
      η / G ≤ ‖euclideanVector (coordinateGradient F (x + θ • (z - x)))‖ := by
    intro hgq
    exact PlanarObjectiveField.gradient_norm_lower_of_visibility hG (hW _ hqQ)
      (hvis _ hqQ _ (convex_supporting_inequality hF (hasFDerivAt_coordinateGradient hgq)))
  obtain ⟨D', hD', hbound⟩ := PlanarObjectiveField.field_determinant_right_derivative_bound hF hχ
    hs0 (hv _ hqQ) (hstruct _ hqQ) hφr hκ hμ hglower (hM _ hqQ) (hvel _ hqQ) htr
  have hderivD := hD'.Ioi_of_Ici.derivWithin (uniqueDiffWithinAt_Ioi θ)
  refine ⟨?_, ?_⟩
  · simpa only [hderivD] using hD'
  · simpa only [hderivD] using hbound

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/disp/028` (`companion/chapters/09_C.tex:288-291`), equation `C:eq:variation`,
in the proof of Lemma `C:lem:transport`: "Set $h(\theta)=\log|D(\theta)|$. Convexity and
$\varphi'(0)=-d$ imply $\varphi'_+(\theta)\ge-d$, and hence
\[ |h'_+(\theta)|\le C|\varphi'_+(\theta)|\le C(\varphi'_+(\theta)+2d)." \]
Under the standing assumptions of §§4-5, for an eligible pair (gradients `g`, `gz`) with
$s=z-x$, $d=-g^Ts$, $q,\varphi,D$ as in display `C/09_C/disp/027`, $D$ nonzero on $[0,1]$
(transversality) and the bound of display `C/09_C/disp/027` for this pair with the constant
$C\ge0$: the function $h=\log|D|$ (the variable `hl`) has the right derivative
$h'_+(\theta)$ on $[0,1)$ and the display holds. -/
theorem log_variation_bound (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (w : Vec 2 → Vec 2) (x z g gz : Vec 2) (hp : EligiblePair F c₁ c₂ x z g gz)
    (s : Vec 2) (hs : s = z - x) (d : ℝ) (hd : d = -dot g s) (q : ℝ → Vec 2)
    (hq : q = fun θ => x + θ • s) (φ D hl : ℝ → ℝ) (hφ : φ = fun θ => F (q θ))
    (_hD : D = fun θ => pairDet s (w (q θ))) (hhl : hl = fun θ => Real.log |D θ|)
    (hD0 : ∀ θ ∈ Icc (0 : ℝ) 1, D θ ≠ 0) (Cq : ℝ) (hCq : 0 ≤ Cq)
    (hquot : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt D (derivWithin D (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin D (Ioi θ) θ / D θ| ≤ Cq * |derivWithin φ (Ioi θ) θ|) :
    ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt hl (derivWithin hl (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin hl (Ioi θ) θ| ≤ Cq * |derivWithin φ (Ioi θ) θ| ∧
      Cq * |derivWithin φ (Ioi θ) θ| ≤ Cq * (derivWithin φ (Ioi θ) θ + 2 * d) := by
  intro θ hθ
  obtain ⟨hD', hbd⟩ := hquot θ hθ
  have hDθ : D θ ≠ 0 := hD0 θ (Ico_subset_Icc_self hθ)
  have hH' : HasDerivWithinAt hl (derivWithin D (Ioi θ) θ / D θ) (Ici θ) θ := by
    rw [hhl]
    simpa only [Real.log_abs] using hD'.log hDθ
  have hderivH := hH'.Ioi_of_Ici.derivWithin (uniqueDiffWithinAt_Ioi θ)
  have hφc : ConvexOn ℝ univ φ := by
    have hc := hF.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x + s))
    rw [hφ, hq]
    simpa only [AffineMap.lineMap_apply_module', add_sub_cancel_left, Function.comp_def,
      Set.preimage_univ, add_comm] using hc
  have h0 : HasDerivAt φ (-d) 0 := by
    have hl : HasDerivAt (fun τ : ℝ => x + τ • s) s 0 := by
      simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add x
    have hcomp := hp.gradient_x.comp_hasDerivAt_of_eq 0 hl (by simp)
    rw [hφ, hq, hd]
    rw [hs] at hcomp ⊢
    simpa only [gradientFunctional_apply, neg_neg] using hcomp
  have hlower := PlanarScalarTransport.convex_right_derivative_lower hφc h0 hθ.1
  have hd0 : 0 ≤ d := by
    rw [hd, hs]
    exact hp.decrease_pos.le
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hderivH] using hH'
  · rw [hderivH]
    exact hbd
  · apply mul_le_mul_of_nonneg_left _ hCq
    rw [abs_le]
    constructor <;> linarith

/-- Item `C/09_C/disp/029` (`companion/chapters/09_C.tex:293-295`), in the proof of Lemma
`C:lem:transport`: the barrier
\[ B(\theta)=C[\varphi(\theta)-\varphi(0)+2d\theta]. \] -/
def barrier (Cq d : ℝ) (φ : ℝ → ℝ) (θ : ℝ) : ℝ := Cq * (φ θ - φ 0 + 2 * d * θ)

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate HomogeneousPlanar in
/-- Item `C/09_C/disp/029` (`companion/chapters/09_C.tex:293-295`), the claims made about the
barrier (lines 292, 296): "Apply the one-sided derivative comparison theorem to the continuous
observable $h-h(0)$ and the barrier $B$. The initial value is zero and the right-derivative norm
is bounded by $B'_+$. Thus $|h(1)-h(0)|\le B(1)\le2Cd$, since $\varphi(1)\le\varphi(0)$."

In the setting of display `C/09_C/disp/028`, with $D$ continuous on $[0,1]$ and the conclusion of
that display: $B(0)=0$; on $[0,1)$, $B$ has the right derivative $B'_+=C(\varphi'_++2d)$ and
$|h'_+|\le B'_+$; and $|h(1)-h(0)|\le B(1)\le2Cd$. -/
theorem barrier_comparison (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (w : Vec 2 → Vec 2) (x z g gz : Vec 2) (hp : EligiblePair F c₁ c₂ x z g gz)
    (s : Vec 2) (hs : s = z - x) (d : ℝ) (_hd : d = -dot g s) (q : ℝ → Vec 2)
    (hq : q = fun θ => x + θ • s) (φ D hl : ℝ → ℝ) (hφ : φ = fun θ => F (q θ))
    (_hD : D = fun θ => pairDet s (w (q θ))) (hhl : hl = fun θ => Real.log |D θ|)
    (hDcont : ContinuousOn D (Icc 0 1)) (hD0 : ∀ θ ∈ Icc (0 : ℝ) 1, D θ ≠ 0)
    (Cq : ℝ) (hCq : 0 ≤ Cq)
    (hbound : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt hl (derivWithin hl (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin hl (Ioi θ) θ| ≤ Cq * |derivWithin φ (Ioi θ) θ| ∧
      Cq * |derivWithin φ (Ioi θ) θ| ≤ Cq * (derivWithin φ (Ioi θ) θ + 2 * d)) :
    barrier Cq d φ 0 = 0 ∧
      (∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (barrier Cq d φ)
          (Cq * (derivWithin φ (Ioi θ) θ + 2 * d)) (Ici θ) θ ∧
        |derivWithin hl (Ioi θ) θ| ≤ Cq * (derivWithin φ (Ioi θ) θ + 2 * d)) ∧
      |hl 1 - hl 0| ≤ barrier Cq d φ 1 ∧ barrier Cq d φ 1 ≤ 2 * Cq * d := by
  have hφc : ConvexOn ℝ univ φ := by
    have hc := hF.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x + s))
    rw [hφ, hq]
    simpa only [AffineMap.lineMap_apply_module', add_sub_cancel_left, Function.comp_def,
      Set.preimage_univ, add_comm] using hc
  have hHcont : ContinuousOn hl (Icc 0 1) := by
    rw [hhl]
    simpa only [Real.log_abs] using hDcont.log hD0
  have hφ' : φ = fun θ => F (x + θ • s) := by rw [hφ, hq]
  have hplus := (BfgsCoverage.Article.PlanarGeometry.comparison_core hF x s d φ hl hφ' hHcont Cq
    hbound 1 (Or.inl rfl) _ rfl).2.2
  have hminus := (BfgsCoverage.Article.PlanarGeometry.comparison_core hF x s d φ hl hφ' hHcont Cq
    hbound (-1) (Or.inr rfl) _ rfl).2.2
  have hdesc : φ 1 ≤ φ 0 := by
    have harm := hp.armijo
    have hc := mul_pos hc₁ hp.decrease_pos
    rw [hφ, hq, hs]
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel]
    linarith
  refine ⟨by simp [barrier], fun θ hθ => ⟨?_, ?_⟩, ?_, ?_⟩
  · have hφr : HasDerivWithinAt φ (derivWithin φ (Ioi θ) θ) (Ici θ) θ :=
      (hφc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)).Ici_of_Ioi
    have h := ((hφr.sub_const (φ 0)).add
      ((hasDerivWithinAt_id θ (Ici θ)).const_mul (2 * d))).const_mul Cq
    convert h using 1
    simp only [id, mul_one]
  · obtain ⟨-, h1, h2⟩ := hbound θ hθ
    exact h1.trans h2
  · simp only [barrier] at hplus hminus ⊢
    rw [abs_le]
    constructor <;> nlinarith
  · simp only [barrier]
    nlinarith

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate in
/-- Item `C/09_C/disp/031` (`companion/chapters/09_C.tex:310-312`), equation `C:eq:numerator`,
in the proof of Lemma `C:lem:secant`: "For different active branches $i,j$ in a two-branch
chart, the segment has a tie point $p$. At that point the jump is orthogonal to $w(p)$. The
branch gradients and $w$ are Lipschitz, so
\[ |y^Tw(z)|\le C_1\norm{s}." \]
Under the standing assumptions of §§4-5: a two-branch chart is an open convex $V$ with
$F=\max\{f_0,f_1\}$ on $V$ (branches indexed by `Fin 2`), convex $C^2$ branches whose gradients
are $L$-Lipschitz and bounded by $H_b$ on $V$; $w$ is $B_w$-Lipschitz, bounded by $G$ and has the
common pairing on $V$ (Euclidean norms). Then one $C_1\ge0$ works for every eligible pair
$x,z\in V$ using branch $i$ at $x$ and a different branch $j$ at $z$. -/
theorem numerator_bound (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (f : Fin 2 → Vec 2 → ℝ) (V : Set (Vec 2)) (hVconv : Convex ℝ V) (hVopen : IsOpen V)
    (_hfconv : ∀ i, ConvexOn ℝ V (f i)) (hfC : ∀ i, ContDiffOn ℝ 2 (f i) V)
    (hmax : ∀ u ∈ V, F u = max (f 0 u) (f 1 u)) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ L * ‖euclideanVector (u - u')‖)
    (Hb : ℝ) (hgradB : ∀ i, ∀ u ∈ V, ‖euclideanVector (coordinateGradient (f i) u)‖ ≤ Hb)
    (w : Vec 2 → Vec 2) (Bw G : ℝ)
    (hwLip : ∀ u ∈ V, ∀ u' ∈ V,
      ‖euclideanVector (w u - w u')‖ ≤ Bw * ‖euclideanVector (u - u')‖)
    (hwB : ∀ u ∈ V, ‖euclideanVector (w u)‖ ≤ G)
    (hcommon : ∀ p ∈ V, ∀ a ∈ subdifferential F p, ∀ b ∈ subdifferential F p,
      dot a (w p) = dot b (w p)) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ x z g h : Vec 2, x ∈ V → z ∈ V → EligiblePair F c₁ c₂ x z g h →
      ∀ i j : Fin 2, i ≠ j → f i x = F x → f j z = F z →
        |dot (h - g) (w z)| ≤ C₁ * ‖euclideanVector (z - x)‖ := by
  by_cases hV : V.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hV
    have hHb : 0 ≤ Hb := (norm_nonneg _).trans (hgradB 0 u₀ hu₀)
    have hG : 0 ≤ G := (norm_nonneg _).trans (hwB u₀ hu₀)
    set Bw' := max Bw 0
    have hwLip' : ∀ u ∈ V, ∀ u' ∈ V,
        ‖euclideanVector (w u - w u')‖ ≤ Bw' * ‖euclideanVector (u - u')‖ := fun u hu u' hu' =>
      (hwLip u hu u' hu').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    refine ⟨2 * L * G + 2 * Hb * Bw', by positivity, ?_⟩
    intro x z g h hx hz hp i j hij hi hj
    exact BfgsCoverage.Article.PlanarGeometry.crossing_core hF f V hVconv hVopen hfC
      (fun u hu => BfgsCoverage.Article.PlanarGeometry.isGreatest_of_max f (hmax u hu))
      L Hb hL.le hHb hLip hgradB w Bw' G (le_max_right _ _) hG hwLip' hwB hcommon x z g h hx hz
      hp.gradient_x hp.gradient_z i j hij hi hj
  · refine ⟨0, le_rfl, ?_⟩
    intro x _ _ _ hx
    exact absurd ⟨x, hx⟩ hV

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate in
/-- Item `C/09_C/disp/032` (`companion/chapters/09_C.tex:314-316`), in the proof of Lemma
`C:lem:secant`: "For the denominator put $a=\nabla f_i(x)$, $b=\nabla f_j(x)$, and
$r=\nabla f_j(z)-\nabla f_j(x)$, with $\norm{r}\le L\norm{s}$. Then
\[ a^Ts=-d,\qquad b^Ts=t-d-r^Ts." \]
In the setting of display `C/09_C/disp/031` (chart and pair), with $s=z-x$, $y=h-g$,
$d=-g^Ts$, $t=y^Ts$ and $a,b,r$ as variables with their definitions. -/
theorem crossing_identities (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (f : Fin 2 → Vec 2 → ℝ) (V : Set (Vec 2)) (_hVconv : Convex ℝ V) (hVopen : IsOpen V)
    (_hfconv : ∀ i, ConvexOn ℝ V (f i)) (hfC : ∀ i, ContDiffOn ℝ 2 (f i) V)
    (hmax : ∀ u ∈ V, F u = max (f 0 u) (f 1 u)) (L : ℝ) (_hL : 0 < L)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ L * ‖euclideanVector (u - u')‖)
    (x z g h : Vec 2) (hx : x ∈ V) (hz : z ∈ V) (hp : EligiblePair F c₁ c₂ x z g h)
    (i j : Fin 2) (_hij : i ≠ j) (hi : f i x = F x) (hj : f j z = F z)
    (s y : Vec 2) (hs : s = z - x) (hy : y = h - g) (d t : ℝ) (hd : d = -dot g s)
    (ht : t = dot y s) (a b r : Vec 2) (ha : a = coordinateGradient (f i) x)
    (hb : b = coordinateGradient (f j) x)
    (hr : r = coordinateGradient (f j) z - coordinateGradient (f j) x) :
    ‖euclideanVector r‖ ≤ L * ‖euclideanVector s‖ ∧ dot a s = -d ∧ dot b s = t - d - dot r s := by
  subst ha hb
  exact BfgsCoverage.Article.PlanarGeometry.crossing_pairings_core hF f V hVopen hfC
    (fun u hu => BfgsCoverage.Article.PlanarGeometry.isGreatest_of_max f (hmax u hu)) L hLip x z g
    h hx hz hp.gradient_x hp.gradient_z i j hi hj s y hs hy d t hd ht r hr

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate in
/-- Item `C/09_C/disp/033` (`companion/chapters/09_C.tex:318-321`), in the proof of Lemma
`C:lem:secant`: "The two gradient rows are uniformly independent on the chart. Thus
\[ \norm{s}\le A(2d+t+L\norm{s}^2)\le A\Bigl(1+\frac{2}{1-c_2}\Bigr)t+AL\norm{s}^2." \]
In the setting of display `C/09_C/disp/032`, with the uniform inverse bound
$\norm{u}\le A(|\nabla f_0(x')^Tu|+|\nabla f_1(x')^Tu|)$ for all $u$ and $x'\in V$ (the rows are
uniformly independent). -/
theorem crossing_inequalities (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ)
    (_hCcpt : IsCompact C) (_hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (f : Fin 2 → Vec 2 → ℝ) (V : Set (Vec 2)) (_hVconv : Convex ℝ V) (hVopen : IsOpen V)
    (_hfconv : ∀ i, ConvexOn ℝ V (f i)) (hfC : ∀ i, ContDiffOn ℝ 2 (f i) V)
    (hmax : ∀ u ∈ V, F u = max (f 0 u) (f 1 u)) (L : ℝ) (_hL : 0 < L)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ L * ‖euclideanVector (u - u')‖)
    (A : ℝ) (hA : 0 ≤ A)
    (hrows : ∀ u ∈ V, ∀ v : Vec 2, ‖euclideanVector v‖ ≤
      A * (|dot (coordinateGradient (f 0) u) v| + |dot (coordinateGradient (f 1) u) v|))
    (x z g h : Vec 2) (hx : x ∈ V) (hz : z ∈ V) (hp : EligiblePair F c₁ c₂ x z g h)
    (i j : Fin 2) (hij : i ≠ j) (hi : f i x = F x) (hj : f j z = F z)
    (s y : Vec 2) (hs : s = z - x) (hy : y = h - g) (d t : ℝ) (hd : d = -dot g s)
    (ht : t = dot y s) (r : Vec 2)
    (hr : r = coordinateGradient (f j) z - coordinateGradient (f j) x) :
    ‖euclideanVector s‖ ≤ A * (2 * d + t + L * ‖euclideanVector s‖ ^ 2) ∧
      A * (2 * d + t + L * ‖euclideanVector s‖ ^ 2) ≤
        A * (1 + 2 / (1 - c₂)) * t + A * L * ‖euclideanVector s‖ ^ 2 := by
  obtain ⟨hrM, hia, hjb⟩ := BfgsCoverage.Article.PlanarGeometry.crossing_pairings_core hF f V
    hVopen hfC (fun u hu => BfgsCoverage.Article.PlanarGeometry.isGreatest_of_max f (hmax u hu))
    L hLip x z g h hx hz hp.gradient_x hp.gradient_z i j hi hj s y hs hy d t hd ht r hr
  have hd0 : 0 ≤ d := by rw [hd, hs]; exact hp.decrease_pos.le
  have hσ : 0 < 1 - c₂ := sub_pos.mpr hc₂
  have hwolfe : (1 - c₂) * d ≤ t := by
    rw [hd, ht, hs, hy]
    exact hp.curvature
  have ht0 : 0 ≤ t := le_trans (mul_nonneg hσ.le hd0) hwolfe
  have hrows' : ‖euclideanVector s‖ ≤ A * (|dot (coordinateGradient (f i) x) s| +
      |dot (coordinateGradient (f j) x) s|) := by
    have h0 := hrows x hx s
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using h0
    · simpa [add_comm] using h0
    · exact absurd rfl hij
  have hrs : |dot r s| ≤ L * ‖euclideanVector s‖ ^ 2 := by
    calc |dot r s| ≤ ‖euclideanVector r‖ * ‖euclideanVector s‖ :=
          PlanarCrossing.abs_dot_le_euclidean_norm r s
      _ ≤ L * ‖euclideanVector s‖ * ‖euclideanVector s‖ :=
          mul_le_mul_of_nonneg_right hrM (norm_nonneg _)
      _ = L * ‖euclideanVector s‖ ^ 2 := by ring
  have hb : |dot (coordinateGradient (f j) x) s| ≤ t + d + L * ‖euclideanVector s‖ ^ 2 := by
    rw [hjb]
    calc |t - d - dot r s| ≤ |t - d| + |dot r s| := abs_sub _ _
      _ ≤ (|t| + |d|) + |dot r s| := by gcongr; exact abs_sub _ _
      _ ≤ t + d + L * ‖euclideanVector s‖ ^ 2 := by
          rw [abs_of_nonneg ht0, abs_of_nonneg hd0]; gcongr
  refine ⟨?_, ?_⟩
  · calc ‖euclideanVector s‖ ≤ A * (|dot (coordinateGradient (f i) x) s| +
          |dot (coordinateGradient (f j) x) s|) := hrows'
      _ ≤ A * (d + (t + d + L * ‖euclideanVector s‖ ^ 2)) := by
          rw [hia, abs_neg, abs_of_nonneg hd0]
          gcongr
      _ = A * (2 * d + t + L * ‖euclideanVector s‖ ^ 2) := by ring
  · have hdt : d ≤ t / (1 - c₂) := (le_div_iff₀ hσ).mpr (by linarith)
    have h2 : 2 * d + t ≤ (1 + 2 / (1 - c₂)) * t := by
      have : 2 * (t / (1 - c₂)) = 2 / (1 - c₂) * t := by ring
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hA]

/-! ### §6. The BFGS contradiction (lines 333-366)

The displays of the proof of Theorem `C:thm:cluster` are stated under the hypotheses of the
theorem (unused ones named `_`). The contradiction hypothesis (no affine-critical cluster point)
is included only where the display needs the construction near $\Gamma$
(`energy_tail_inequality`); there the assumptions cannot all hold, which is what the proof
shows. The other displays are stated without it, at a given index or for given sequences, so
their assumptions are satisfiable. -/

open AffineCriticalObjective in
/-- Item `C/09_C/disp/034` (`companion/chapters/09_C.tex:338-341`), in the proof of Theorem
`C:thm:cluster`: "Let $B_k=H_k^{-1}$ and
\[ E_k=w(x_k)^TB_kw(x_k),\qquad M_k=B_k-\frac{g_kg_k^T}{q_k}\succeq0,\qquad M_ks_k=0." \]
The display defines $B_k$, $E_k$ (used in display `C/09_C/disp/035`) and $M_k$ (variables with
their defining equations) and asserts $M_k\succeq0$ and $M_ks_k=0$, $s_k=-\alpha_kH_kg_k$. -/
theorem annihilated_matrix (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b})
    (_hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (_hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (_hR : R.x 0 ∈ {x | F x ≤ b})
    (B M : ℕ → Mat 2) (hB : ∀ k, B k = (R.H k)⁻¹)
    (hM : ∀ k, M k = B k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ) :
    (M k).PosSemidef ∧ M k *ᵥ (-R.α k • (R.H k *ᵥ R.g k)) = 0 := by
  have hMk : M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) := by
    rw [hM k, hB k]
    rfl
  rw [hMk]
  exact ⟨R.annihilated_hessian_posSemidef k, R.annihilated_hessian_mul_displacement k⟩

open AffineCriticalObjective in
/-- Item `C/09_C/disp/035` (`companion/chapters/09_C.tex:343-346`), equation `C:eq:energy`, in
the proof of Theorem `C:thm:cluster`: "The Hessian form of \eqref{C:eq:bfgs}, the representation
in Lemma `C:lem:transport`, and $M_ks_k=0$ give the exact identity
\[ E_{k+1}=\lambda_k^2\Bigl(E_k-\frac{(g_k^Tw(x_k))^2}{q_k}\Bigr)
     +\frac{(y_k^Tw(x_{k+1}))^2}{t_k}." \]
Under the hypotheses of the theorem, for a field $w$, $E_k=w(x_k)^TH_k^{-1}w(x_k)$ and an index
$k$ at which $w(x_{k+1})=\lambda_kw(x_k)+\beta_ks_k$ ($s_k=x_{k+1}-x_k$); with the next sentence
"The parenthesized expression is nonnegative". -/
theorem energy_identity (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b})
    (_hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (_hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (_hR : R.x 0 ∈ {x | F x ≤ b})
    (w : Vec 2 → Vec 2) (E : ℕ → ℝ) (hE : ∀ k, E k = dot (w (R.x k)) ((R.H k)⁻¹ *ᵥ w (R.x k)))
    (k : ℕ) (lam β : ℝ) (_hlam : 0 < lam)
    (hframe : w (R.x (k + 1)) = lam • w (R.x k) + β • (R.x (k + 1) - R.x k)) :
    E (k + 1) = lam ^ 2 * (E k - (dot (R.g k) (w (R.x k))) ^ 2 / R.q k) +
        (dot (R.g (k + 1) - R.g k) (w (R.x (k + 1)))) ^ 2 /
          dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) ∧
      0 ≤ E k - (dot (R.g k) (w (R.x k))) ^ 2 / R.q k := by
  have hdisp : R.displacement k = R.x (k + 1) - R.x k := by
    rw [R.step]; simp [AdmissibleBFGSRun.displacement]
  have hen := R.scalar_frame_energy k (w (R.x k)) (w (R.x (k + 1))) lam β
    (by rw [hdisp]; exact hframe)
  have hres := R.scalar_frame_residual_nonneg k (w (R.x k))
  have hEk : ∀ j, E j = metricEnergy (R.hessian j) (w (R.x j)) := fun j => by
    rw [hE j]; rfl
  simp only [AdmissibleBFGSRun.gradientChange, AdmissibleBFGSRun.curvature, hdisp] at hen
  rw [← hEk, ← hEk] at hen
  rw [← hEk] at hres
  exact ⟨hen, hres⟩

open AffineCriticalObjective in
/-- Item `C/09_C/disp/036` (`companion/chapters/09_C.tex:348-351`), in the proof of Theorem
`C:thm:cluster`, the step: at an index $k$ where uniform visibility
($(g_k^Tw(x_k))^2\ge m$), the secant bound ($(y_k^Tw(x_{k+1}))^2/t_k\le C_0$) and the transport
of Lemma `C:lem:transport` ($w(x_{k+1})=\lambda_kw(x_k)+\beta_ks_k$, $\lambda_k^2\le1+Cd_k$)
hold,
\[ E_{k+1}\le(1+Cd_k)(E_k-m/q_k)+C_0. \]
(`energy_tail_inequality` states that these facts hold on a tail.) -/
theorem energy_step_inequality (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b})
    (w : Vec 2 → Vec 2) (E : ℕ → ℝ) (hE : ∀ k, E k = dot (w (R.x k)) ((R.H k)⁻¹ *ᵥ w (R.x k)))
    (m Cd C₀ : ℝ) (k : ℕ) (lam β : ℝ) (hlam : 0 < lam)
    (hframe : w (R.x (k + 1)) = lam • w (R.x k) + β • (R.x (k + 1) - R.x k))
    (hvis : m ≤ (dot (R.g k) (w (R.x k))) ^ 2)
    (hsec : (dot (R.g (k + 1) - R.g k) (w (R.x (k + 1)))) ^ 2 /
      dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) ≤ C₀)
    (htr : lam ^ 2 ≤ 1 + Cd * R.d k) :
    E (k + 1) ≤ (1 + Cd * R.d k) * (E k - m / R.q k) + C₀ := by
  obtain ⟨h1, h2⟩ := BfgsCoverage.Article.Local.planar_cluster_energy F hF Fstar hFstar b hb hK
    hstrict hreg R hR w E hE m C₀ Cd k lam β hlam hframe hvis hsec htr
  rw [h1]
  exact h2

open AffineCriticalObjective TransportedCertificate in
/-- Item `C/09_C/disp/036` (`companion/chapters/09_C.tex:348-351`), in the proof of Theorem
`C:thm:cluster`: "Uniform visibility and the last two lemmas imply, on a tail,
\[ E_{k+1}\le(1+Cd_k)(E_k-m/q_k)+C_0,\qquad m>0." \]
Under the hypotheses of the theorem, for an admissible run starting in $K$ whose cluster set
contains no affine-critical point (the contradiction hypothesis of the proof): there are a field
$w$ (constructed near $\Gamma$), constants $m>0$, $C,C_0\ge0$ and an index $K_0$ such that, with
$E_k=w(x_k)^TH_k^{-1}w(x_k)$, the inequality holds for every $k\ge K_0$. (These assumptions
cannot all hold: that is the contradiction the proof derives.) -/
theorem energy_tail_inequality (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (hb : Fstar < b)
    (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (hR : R.x 0 ∈ {x | F x ≤ b})
    (hnoaff : ∀ p, MapClusterPt p atTop R.x → ¬ IsAffineCritical F p) :
    ∃ (w : Vec 2 → Vec 2) (m Cd C₀ : ℝ) (K₀ : ℕ), 0 < m ∧ 0 ≤ Cd ∧ 0 ≤ C₀ ∧
      ∀ k, K₀ ≤ k →
        dot (w (R.x (k + 1))) ((R.H (k + 1))⁻¹ *ᵥ w (R.x (k + 1))) ≤
          (1 + Cd * R.d k) * (dot (w (R.x k)) ((R.H k)⁻¹ *ᵥ w (R.x k)) - m / R.q k) + C₀ := by
  obtain ⟨-, -, ℓ, hℓpos, -, hℓ, -, hsteps⟩ := contradiction_setup F hF Fstar hFstar b hb hK hstrict
    hreg R hR hnoaff
  obtain ⟨w, U, hU, hΓU, -, m, C, L, δ, hm, hC, hL, hδ, hpairs⟩ :=
    BfgsCoverage.Article.Local.planar_cluster_field F hF Fstar hFstar b hb hK hstrict hreg R hR ℓ hℓ
      hℓpos hnoaff
  have hxK : ∀ k, R.x k ∈ {x | F x ≤ b} := fun k => le_trans (R.objective_le_initial k) hR
  have hevU : ∀ᶠ k in atTop, R.x k ∈ U :=
    ClusterSetGeometry.eventually_mem_of_open_superset R.x hK hxK hU hΓU
  have hstep : ∀ k, -R.α k • (R.H k *ᵥ R.g k) = R.x (k + 1) - R.x k := fun k => by
    rw [R.step k]
    simp [bfgsStep]
  have hsmall : ∀ᶠ k in atTop, ‖euclideanVector (R.x (k + 1) - R.x k)‖ < δ := by
    have hc : Continuous fun v : Vec 2 => ‖euclideanVector v‖ :=
      (PiLp.continuous_equiv_symm _ _).norm
    have ht := (hc.tendsto 0).comp hsteps
    simp only [Function.comp_def, hstep] at ht
    have h0 : ‖euclideanVector (0 : Vec 2)‖ = 0 := by simp [euclideanVector]
    rw [h0] at ht
    exact ht.eventually (gt_mem_nhds hδ)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (hevU.and ((tendsto_add_atTop_nat 1).eventually hevU |>.and hsmall))
  refine ⟨w, m, L, C, K₀, hm, hL, hC, fun k hk => ?_⟩
  obtain ⟨hxU, hzU, hs⟩ := hK₀ k hk
  obtain ⟨hpair, hd, -⟩ := BfgsCoverage.Article.Energy.accepted_pairs_eligible R k
  obtain ⟨lam, β, hlam, hvis, hsec, hframe, htr⟩ :=
    hpairs (R.x k) hxU (R.x (k + 1)) hzU (R.g k) (R.g (k + 1)) hpair hs
  rw [hd] at htr
  exact energy_step_inequality F hF Fstar hFstar b hb hK hstrict hreg R hR w
    (fun j => dot (w (R.x j)) ((R.H j)⁻¹ *ᵥ w (R.x j))) (fun _ => rfl) m L C k lam β hlam hframe
    hvis hsec htr

/-- The telescoping of display `C/09_C/disp/037` for real sequences: if $E_k\ge0$, $q_k>0$,
$d_k\ge0$, $m>0$, $C,C_0\ge0$, $E_{k+1}\le(1+Cd_k)(E_k-m/q_k)+C_0$ for $k\ge K$, $P_K=1$,
$P_{k+1}=P_k(1+Cd_k)$ and $P_k\le\bar P$ for $k\ge K$, then
$\frac m{\bar P}\sum_{k=K}^{N-1}\frac1{q_k}\le E_K+C_0(N-K)$ for $N\ge K$. -/
theorem telescoping_algebra (E q d P : ℕ → ℝ) (m Cd C₀ Pbar : ℝ) (K : ℕ)
    (hE : ∀ k, 0 ≤ E k) (hq : ∀ k, 0 < q k) (hd : ∀ k, 0 ≤ d k) (hm : 0 < m) (hCd : 0 ≤ Cd)
    (hC₀ : 0 ≤ C₀)
    (htail : ∀ k, K ≤ k → E (k + 1) ≤ (1 + Cd * d k) * (E k - m / q k) + C₀)
    (hPK : P K = 1) (hPs : ∀ k, K ≤ k → P (k + 1) = P k * (1 + Cd * d k))
    (hPbar : ∀ k, K ≤ k → P k ≤ Pbar) :
    ∀ N, K ≤ N → m / Pbar * ∑ k ∈ Finset.Ico K N, (q k)⁻¹ ≤ E K + C₀ * ((N : ℝ) - K) := by
  have hP1 : ∀ k, K ≤ k → 1 ≤ P k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [hPK]
    | succ k hk ih =>
      rw [hPs k hk]
      have : 1 ≤ 1 + Cd * d k := by nlinarith [hd k]
      nlinarith
  have hstep : ∀ k, K ≤ k → E (k + 1) / P (k + 1) + m / (q k * P k) ≤ E k / P k + C₀ := by
    intro k hk
    have hPk := hP1 k hk
    have hPk0 : 0 < P k := by linarith
    have ha : 1 ≤ 1 + Cd * d k := by nlinarith [hd k]
    have hpos : 0 < P k * (1 + Cd * d k) := by positivity
    have hqk := hq k
    rw [hPs k hk]
    have h1 : E (k + 1) / (P k * (1 + Cd * d k)) ≤
        ((1 + Cd * d k) * (E k - m / q k) + C₀) / (P k * (1 + Cd * d k)) :=
      div_le_div_of_nonneg_right (htail k hk) hpos.le
    have h2 : ((1 + Cd * d k) * (E k - m / q k) + C₀) / (P k * (1 + Cd * d k)) =
        E k / P k - m / (q k * P k) + C₀ / (P k * (1 + Cd * d k)) := by
      field_simp
      ring
    have h3 : C₀ / (P k * (1 + Cd * d k)) ≤ C₀ := div_le_self hC₀ (by nlinarith)
    linarith
  have hsum : ∀ N, K ≤ N → E N / P N + m * ∑ k ∈ Finset.Ico K N, (q k * P k)⁻¹ ≤
      E K + C₀ * ((N : ℝ) - K) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp [hPK]
    | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, mul_add]
      have h := hstep N hN
      have he : m * (q N * P N)⁻¹ = m / (q N * P N) := by rw [div_eq_mul_inv]
      push_cast
      linarith
  intro N hN
  have hPbar0 : 0 < Pbar := lt_of_lt_of_le one_pos ((hP1 K le_rfl).trans (hPbar K le_rfl))
  have hEN : 0 ≤ E N / P N := div_nonneg (hE N) (by linarith [hP1 N hN])
  have hcmp : m / Pbar * ∑ k ∈ Finset.Ico K N, (q k)⁻¹ ≤
      m * ∑ k ∈ Finset.Ico K N, (q k * P k)⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hm.le
    apply Finset.sum_le_sum
    intro k hk
    have hkK : K ≤ k := (Finset.mem_Ico.mp hk).1
    have hPk := hP1 k hkK
    have hqk := hq k
    rw [mul_inv]
    rw [mul_comm (Pbar⁻¹) (q k)⁻¹]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hqk.le)
    exact inv_anti₀ (by linarith) (hPbar k hkK)
  linarith [hsum N hN]

open AffineCriticalObjective in
/-- Item `C/09_C/disp/037` (`companion/chapters/09_C.tex:353-356`), in the proof of Theorem
`C:thm:cluster`: "Set $P_K=1$ and $P_{k+1}=P_k(1+Cd_k)$. Since $\sum d_k<\infty$,
$1\le P_k\le\bar P<\infty$. Divide by $P_{k+1}$ and telescope. Positivity gives
\[ \frac{m}{\bar P}\sum_{k=K}^{N-1}\frac1{q_k}\le E_K+C_0(N-K)." \]
Under the hypotheses of the theorem, for a field $w$, $E_k=w(x_k)^TH_k^{-1}w(x_k)$, constants
$m>0$, $C,C_0\ge0$, the inequality of display `C/09_C/disp/036` for $k\ge K$, $P$ with its
defining equations and a bound $\bar P$ of $P_k$ ($k\ge K$): the display holds for every
$N\ge K$. Positivity is $E_N\ge0$ ($H_N^{-1}\succ0$). For a run starting in $K$ these
assumptions cannot all hold (by Chapter M's reciprocal growth, `gradients_bounded_M_applies`):
that is the contradiction the proof derives next; `telescoping_algebra` is the same inequality
for arbitrary sequences. -/
theorem telescoped_bound (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (_hb : Fstar < b)
    (_hK : IsCompact {x | F x ≤ b})
    (_hstrict : ∀ t, Fstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (_hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (R : AdmissibleBFGSRun 2 F) (_hR : R.x 0 ∈ {x | F x ≤ b})
    (w : Vec 2 → Vec 2) (E : ℕ → ℝ) (hE : ∀ k, E k = dot (w (R.x k)) ((R.H k)⁻¹ *ᵥ w (R.x k)))
    (m Cd C₀ : ℝ) (hm : 0 < m) (hCd : 0 ≤ Cd) (hC₀ : 0 ≤ C₀) (K : ℕ)
    (htail : ∀ k, K ≤ k → E (k + 1) ≤ (1 + Cd * R.d k) * (E k - m / R.q k) + C₀)
    (P : ℕ → ℝ) (hPK : P K = 1) (hPs : ∀ k, K ≤ k → P (k + 1) = P k * (1 + Cd * R.d k))
    (Pbar : ℝ) (hPbar : ∀ k, K ≤ k → P k ≤ Pbar) :
    ∀ N, K ≤ N → m / Pbar * ∑ k ∈ Finset.Ico K N, (R.q k)⁻¹ ≤ E K + C₀ * ((N : ℝ) - K) := by
  have hEpos : ∀ k, 0 ≤ E k := by
    intro k
    have hres := R.scalar_frame_residual_nonneg k (w (R.x k))
    have hEk : E k = metricEnergy (R.hessian k) (w (R.x k)) := by rw [hE k]; rfl
    rw [hEk]
    have : 0 ≤ (dot (R.g k) (w (R.x k))) ^ 2 / R.q k := div_nonneg (sq_nonneg _) (R.q_pos k).le
    linarith
  exact telescoping_algebra E R.q R.d P m Cd C₀ Pbar K hEpos R.q_pos (fun k => (R.d_pos k).le) hm
    hCd hC₀ htail hPK hPs hPbar

/-! ### §7. Local consequences and natural assumptions (lines 370-404) -/

open ConvexSubdifferential AffineCriticalObjective in
/-- Item `C/09_C/disp/038` (`companion/chapters/09_C.tex:378-380`), in the proof of Corollary
`C:cor:max`: "Form the augmented matrix $A(x)$ whose columns are $(\nabla f_i(x),1)$ for
$i\in I_*$. Affine independence makes $A(x_*)$ full column rank; that rank persists. Whenever
$A(p)\lambda=(0,0,1)^T$ has a solution, it is unique and equals
\[ (A(p)^TA(p))^{-1}A(p)^T(0,0,1)^T." \]
Under the hypotheses of the corollary, with $A$ the variable with its defining equation. -/
theorem gram_formula (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (xstar : Vec 2)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    {m : ℕ} (f : Fin m → Vec 2 → ℝ) (U : Set (Vec 2)) (hU : IsOpen U) (hxU : xstar ∈ U)
    (hf : ∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U)
    (hmax : ∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x))
    (hcontour : ∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (I : Finset (Fin m)) (hI : I = Finset.univ.filter fun i => f i xstar = F xstar)
    (hind : AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar)
    (lam : I → ℝ) (hpos : ∀ i, 0 < lam i) (hsum : ∑ i, lam i = 1)
    (hzero : ∑ i, lam i • coordinateGradient (f i) xstar = 0)
    (A : Vec 2 → Matrix (Fin 3) I ℝ)
    (hA : ∀ p, A p = Matrix.of fun (r : Fin 3) (i : I) =>
      ![coordinateGradient (f i) p 0, coordinateGradient (f i) p 1, 1] r) :
    Function.Injective (A xstar).mulVec ∧
      ∀ᶠ p in 𝓝 xstar, Function.Injective (A p).mulVec ∧
        ∀ l : I → ℝ, A p *ᵥ l = ![0, 0, 1] →
          l = ((A p)ᵀ * A p)⁻¹ *ᵥ ((A p)ᵀ *ᵥ ![0, 0, 1]) :=
  BfgsCoverage.Article.Local.planar_max_barycentric F hF xstar hmin huniq f U hU hxU hf hmax
    hcontour I hI hind lam hpos hsum hzero A hA

/-! ### §8. An explicit quadratic example and basin (lines 408-456)

The branches and the objective are variables with their defining equations (`hf`, `hF`), as in
the article's coverage (`Local.example_eq` identifies them with the library's
`PlanarQuadraticExample.branch` and `objective`). -/

/-- Item `C/09_C/prose/074` (`companion/chapters/09_C.tex:416`), anchor "All branch
Hessians lie between $I$ and $3I$."

"All branch Hessians lie between $I$ and $3I$. Also $(f_0+f_1+f_2)/3=u^2+v^2$, so $F\ge u^2+v^2$
and zero is its unique minimizer. At zero the active gradients are $(1,0),(0,1),(-1,-1)$, with
positive weights $1/3$." (`RadialHessian.matrix f x` is the Hessian matrix; the article's
`Local.example_model_facts` also records strict positive contours.) -/
theorem example_model (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    (∀ i x, (RadialHessian.matrix (f i) x - 1).PosSemidef ∧
      ((3 : ℝ) • (1 : Mat 2) - RadialHessian.matrix (f i) x).PosSemidef) ∧
    (∀ x : Vec 2, (f 0 x + f 1 x + f 2 x) / 3 = x 0 ^ 2 + x 1 ^ 2) ∧
    (∀ x : Vec 2, x 0 ^ 2 + x 1 ^ 2 ≤ F x) ∧ F 0 = 0 ∧ (∀ x, F 0 ≤ F x) ∧
    (∀ x, F x = F 0 → x = 0) ∧
    (∀ t, 0 < t → ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
    (∀ i, f i 0 = F 0) ∧
    coordinateGradient (f 0) 0 = ![1, 0] ∧ coordinateGradient (f 1) 0 = ![0, 1] ∧
    coordinateGradient (f 2) 0 = ![-1, -1] ∧
    ∑ i : Fin 3, (1 / 3 : ℝ) • coordinateGradient (f i) 0 = 0 :=
  BfgsCoverage.Article.Local.example_model_facts f hf F hF

/-- Item `C/09_C/disp/040` (`companion/chapters/09_C.tex:419-423`): "The affine coefficient
calculation is exact. With $D=3(1+v-uv)$, the solution of $\sum\lambda_i\nabla f_i=0$,
$\sum\lambda_i=1$ is
\[ \lambda_0=\frac{1-4u+3v-7uv}{D},\quad \lambda_1=\frac{1+2u-3v-uv}{D},\quad
   \lambda_2=\frac{1+2u+3v+5uv}{D}." \]
At a point $(u,v)=(x_0,x_1)$ with $D\ne0$ (as on the box of the next sentence, where
$D\ge267/100$; "the solution" presupposes it): the system has a solution, and every solution is
given by these formulas. -/
theorem example_coefficients_formula (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (x : Vec 2) (D : ℝ)
    (hD : D = 3 * (1 + x 1 - x 0 * x 1)) (hD0 : D ≠ 0) :
    (∃ l : Fin 3 → ℝ, ∑ i, l i = 1 ∧ ∑ i, l i • coordinateGradient (f i) x = 0) ∧
      ∀ l : Fin 3 → ℝ, ∑ i, l i = 1 → ∑ i, l i • coordinateGradient (f i) x = 0 →
        l 0 = (1 - 4 * x 0 + 3 * x 1 - 7 * x 0 * x 1) / D ∧
        l 1 = (1 + 2 * x 0 - 3 * x 1 - x 0 * x 1) / D ∧
        l 2 = (1 + 2 * x 0 + 3 * x 1 + 5 * x 0 * x 1) / D := by
  refine ⟨?_, fun l hl1 hl0 => ?_⟩
  · obtain ⟨hfe, -⟩ := BfgsCoverage.Article.Local.example_eq f hf F hF
    subst hfe
    have hDx : PlanarQuadraticExample.denominator x ≠ 0 := by
      rw [PlanarQuadraticExample.denominator, ← hD]; exact hD0
    refine ⟨PlanarQuadraticExample.coefficients x, PlanarQuadraticExample.coefficients_sum hDx, ?_⟩
    simp only [PlanarQuadraticExample.coordinateGradient_eq]
    exact PlanarQuadraticExample.coefficients_zero hDx
  · obtain ⟨h0, h1, h2⟩ := BfgsCoverage.Article.Local.example_coefficients f hf F hF x D hD l hl1 hl0
    refine ⟨?_, ?_, ?_⟩
    · rw [← h0]; field_simp
    · rw [← h1]; field_simp
    · rw [← h2]; field_simp

/-- Items `C/09_C/prose/076` and `C/09_C/prose/077` (`companion/chapters/09_C.tex:424`),
anchors "On $|u|,|v|\le1/10$, $D\ge267/100$" and "Hence affine independence and local
\eqref{C:eq:AC} hold on this box."

On the box $|u|,|v|\le1/10$: $D=3(1+v-uv)\ge267/100$ and the numerators are at least $23/100$,
$49/100$, $45/100$; the coefficients solve the affine system; the three gradients are affinely
independent and \eqref{C:eq:AC} holds (`AffineCorrectAt`) at every point of the box; also the
regular-switching alternative holds there off $\mathcal C_{\rm aff}$; and $\{F\le1/100\}$ lies in
the box (since $F\ge\norm{x}^2$). (`Local.example_box_facts`.) -/
theorem example_box (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    (∀ x : Vec 2, 3 * (1 + x 1 - x 0 * x 1) = Matrix.det !![
      coordinateGradient (f 0) x 0, coordinateGradient (f 1) x 0, coordinateGradient (f 2) x 0;
      coordinateGradient (f 0) x 1, coordinateGradient (f 1) x 1, coordinateGradient (f 2) x 1;
      1, 1, 1]) ∧
    (∀ x : Vec 2, |x 0| ≤ 1 / 10 → |x 1| ≤ 1 / 10 →
      267 / 100 ≤ 3 * (1 + x 1 - x 0 * x 1) ∧ 23 / 100 ≤ 1 - 4 * x 0 + 3 * x 1 - 7 * x 0 * x 1 ∧
      49 / 100 ≤ 1 + 2 * x 0 - 3 * x 1 - x 0 * x 1 ∧
      45 / 100 ≤ 1 + 2 * x 0 + 3 * x 1 + 5 * x 0 * x 1 ∧
      (∑ i, PlanarQuadraticExample.coefficients x i = 1 ∧
        ∑ i, PlanarQuadraticExample.coefficients x i • coordinateGradient (f i) x = 0) ∧
      AffineIndependent ℝ (fun i => coordinateGradient (f i) x) ∧
      AffineCriticalObjective.AffineCorrectAt F x ∧
      (¬ AffineCriticalObjective.IsAffineCritical F x →
        ContDiffAt ℝ 2 F x ∨ PlanarCornerCharts.ConvexTwoBranchRegularAt F x)) ∧
    ∀ x : Vec 2, F x ≤ 1 / 100 → |x 0| ≤ 1 / 10 ∧ |x 1| ≤ 1 / 10 :=
  BfgsCoverage.Article.Local.example_box_facts f hf F hF

/-- Item `C/09_C/disp/041` (`companion/chapters/09_C.tex:425-427`), equation
`C:eq:explicitbasin`:
\[ F(x_0)<1/100\quad\Longrightarrow\quad x_k\to0 \]
for every infinite admissible full-BFGS run with arbitrary SPD initialization (and arbitrary
valid constants). -/
theorem explicit_basin (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < 1 / 100 → Tendsto R.x atTop (𝓝 0) :=
  fun R hR => ((BfgsCoverage.Article.Local.nonradial_example f hf F hF).1 R hR).2

/-- Item `C/09_C/disp/042` (`companion/chapters/09_C.tex:436-439`), with the surrounding text
(lines 435, 440): "For small $u>0$, the active tie $f_0=f_1$ has
\[ v=v(u)=\frac{-1+\sqrt{1+4u+2u^2}}2=u-\tfrac12u^2+O(u^3), \]
with $f_2$ inactive." With $v$ the variable with its defining equation: the expansion as
$u\to0^+$, and for $0<u<1/10$, $v(u)>0$ and $(u,v(u))$ is a tie $f_0=f_1=F$ with $f_2<F$. -/
theorem tie_curve (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) :
    ((fun u => v u - (u - u ^ 2 / 2)) =O[𝓝[>] 0] (fun u => u ^ 3)) ∧
      ∀ u : ℝ, 0 < u → u < 1 / 10 →
        0 < v u ∧ f 0 ![u, v u] = F ![u, v u] ∧ f 1 ![u, v u] = F ![u, v u] ∧
          f 2 ![u, v u] < F ![u, v u] :=
  ⟨BfgsCoverage.Article.Local.example_tie_expansion v hv,
    fun u hu hu' => BfgsCoverage.Article.Local.example_tie f hf F hF v hv u hu hu'⟩

/-- Item `C/09_C/disp/043` (`companion/chapters/09_C.tex:441-444`): "The gradient jump at the
tie is
\[ \nabla f_0-\nabla f_1=(1+u,-1-2v),\qquad (\nabla f_0-\nabla f_1)^T(u,v)=\tfrac12u^2-v^2\ne0." \]
The jump formula holds at every point $(u,v)$; at the tie point $(u,v(u))$ with $0<u<1/10$ the
radial pairing equals $\frac12u^2-v^2$ and is nonzero. -/
theorem gradient_jump (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) :
    (∀ x : Vec 2, coordinateGradient (f 0) x - coordinateGradient (f 1) x =
      ![1 + x 0, -1 - 2 * x 1]) ∧
    ∀ u : ℝ, 0 < u → u < 1 / 10 →
      dot (coordinateGradient (f 0) ![u, v u] - coordinateGradient (f 1) ![u, v u]) ![u, v u] =
        u ^ 2 / 2 - v u ^ 2 ∧ u ^ 2 / 2 - v u ^ 2 ≠ 0 := by
  refine ⟨fun x => ?_, fun u hu hu' => ?_⟩
  · obtain ⟨hfe, -⟩ := BfgsCoverage.Article.Local.example_eq f hf F hF
    subst hfe
    rw [PlanarQuadraticExample.coordinateGradient_eq, PlanarQuadraticExample.coordinateGradient_eq]
    obtain ⟨g0, g1, -⟩ := PlanarQuadraticExample.gradient_coordinates x
    rw [g0, g1]
    ext i
    fin_cases i <;> simp <;> ring
  · obtain ⟨h1, h2, h3⟩ := BfgsCoverage.Article.Local.example_radial_jump f hf F hF v hv u hu hu'
    exact ⟨h1.trans h2, h3⟩

/-- Item `C/09_C/disp/044` (`companion/chapters/09_C.tex:446-450`), with the preceding sentence
(line 445): "Take $x=(u,v+\epsilon)$ on branch 1 and $z=(u,v-\epsilon)$ on branch 0. Then
$s=(0,-2\epsilon)$ and
\[ d=2\epsilon(1+3v+3\epsilon),\quad t=2\epsilon(1+2v+4\epsilon),\quad
   \Delta=\epsilon(1+4v)+\epsilon^2." \]
For fixed $0<u<1/10$, $v=v(u)$, and all sufficiently small $\epsilon>0$: branch 1 is the only
active branch at $x$ and branch 0 at $z$, so $g=\nabla F(x)=\nabla f_1(x)$ and
$h=\nabla F(z)=\nabla f_0(z)$; $s=z-x=(0,-2\epsilon)$, and with $d=-g^Ts$, $t=(h-g)^Ts$,
$\Delta=F(x)-F(z)$ the three formulas hold. -/
theorem pair_values (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) (u : ℝ) (hu : 0 < u)
    (hu' : u < 1 / 10) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x z g h : Vec 2, x = ![u, v u + ε] → z = ![u, v u - ε] →
      g = coordinateGradient (f 1) x → h = coordinateGradient (f 0) z →
      (f 0 x < f 1 x ∧ f 2 x < f 1 x ∧ f 1 z < f 0 z ∧ f 2 z < f 0 z) ∧
      HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z ∧
      z - x = ![0, -2 * ε] ∧
      -dot g (z - x) = 2 * ε * (1 + 3 * v u + 3 * ε) ∧
      dot (h - g) (z - x) = 2 * ε * (1 + 2 * v u + 4 * ε) ∧
      F x - F z = ε * (1 + 4 * v u) + ε ^ 2 := by
  filter_upwards [BfgsCoverage.Article.Local.example_pair_values f hf F hF v hv u hu hu']
    with ε hε
  intro x z g h hx hz hg hh
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hε x z g h hx hz hg hh
  refine ⟨h1, h2, h3, ?_, h4, h5, h6⟩
  rw [hx, hz]
  ext i
  fin_cases i <;> simp
  ring

/-- Item `C/09_C/prose/078` (`companion/chapters/09_C.tex:451`), anchor "For each
sufficiently small fixed $u>0$ and $\epsilon\downarrow0$, these are eligible".

For each fixed $0<u<1/10$ and all sufficiently small $\epsilon>0$, the pair $x=(u,v+\epsilon)$,
$z=(u,v-\epsilon)$ ($v=v(u)$) with $g=\nabla f_1(x)$, $h=\nabla f_0(z)$ is eligible for
$c_1=1/4$, $c_2=1/2$. -/
theorem pairs_eligible (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) (u : ℝ) (hu : 0 < u)
    (hu' : u < 1 / 10) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TransportedCertificate.EligiblePair F (1 / 4) (1 / 2)
      ![u, v u + ε] ![u, v u - ε] (coordinateGradient (f 1) ![u, v u + ε])
      (coordinateGradient (f 0) ![u, v u - ε]) := by
  obtain ⟨hfe, hFe⟩ := BfgsCoverage.Article.Local.example_eq f hf F hF
  subst hfe hFe
  have hve : v = PlanarQuadraticExample.tieHeight := funext fun u => by
    rw [hv u, PlanarQuadraticExample.tieHeight]
  subst hve
  filter_upwards [PlanarQuadraticExample.eventually_eligible hu hu'] with ε hε
  rw [PlanarQuadraticExample.coordinateGradient_eq, PlanarQuadraticExample.coordinateGradient_eq]
  exact hε

/-- Item `C/09_C/prose/079` (`companion/chapters/09_C.tex:451`), anchor "The radial
numerator tends to the nonzero quantity".

For fixed $0<u<1/10$, as $\epsilon\to0^+$ the radial numerator $(h-g)^Tz$ of the pairs of
`pairs_eligible` tends to $\frac12u^2-v^2\ne0$, while $t=(h-g)^T(z-x)\to0^+$. -/
theorem radial_numerator_limit (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) (v : ℝ → ℝ)
    (hv : ∀ u, v u = (-1 + Real.sqrt (1 + 4 * u + 2 * u ^ 2)) / 2) (u : ℝ) (hu : 0 < u)
    (hu' : u < 1 / 10) :
    Tendsto (fun ε => dot (coordinateGradient (f 0) ![u, v u - ε] -
        coordinateGradient (f 1) ![u, v u + ε]) ![u, v u - ε]) (𝓝[>] 0)
        (𝓝 (u ^ 2 / 2 - v u ^ 2)) ∧ u ^ 2 / 2 - v u ^ 2 ≠ 0 ∧
      Tendsto (fun ε => dot (coordinateGradient (f 0) ![u, v u - ε] -
        coordinateGradient (f 1) ![u, v u + ε]) (![u, v u - ε] - ![u, v u + ε])) (𝓝[>] 0)
        (𝓝[>] 0) := by
  have hne := (BfgsCoverage.Article.Local.example_radial_jump f hf F hF v hv u hu hu').2.2
  obtain ⟨hfe, -⟩ := BfgsCoverage.Article.Local.example_eq f hf F hF
  subst hfe
  have hve : v = PlanarQuadraticExample.tieHeight := funext fun u => by
    rw [hv u, PlanarQuadraticExample.tieHeight]
  subst hve
  refine ⟨?_, hne, ?_⟩
  · have h := PlanarQuadraticExample.radial_numerator_tendsto hu.le
    simp only [RadialCertificate.radialNumerator, sub_zero] at h
    convert h using 2 with ε
    rw [PlanarQuadraticExample.coordinateGradient_eq, PlanarQuadraticExample.coordinateGradient_eq]
    rfl
  · have h := PlanarQuadraticExample.pair_curvature_tendsto hu
    convert h using 2 with ε
    rw [PlanarQuadraticExample.coordinateGradient_eq, PlanarQuadraticExample.coordinateGradient_eq]
    rfl

/-- Item `C/09_C/prose/080` (`companion/chapters/09_C.tex:451`), anchor "Thus RS fails on a
positive band in every neighborhood of zero".

"Thus RS fails on a positive band in every neighborhood of zero, even though
\eqref{C:eq:explicitbasin} holds." RS is the radial secant condition of Chapter R
(`R:eq:RS`): for every $\eta>0$ some $C_\eta$ bounds $N(x,z)^2\le C_\eta T(x,z)$ for
differentiable $x,z$ with $F_*+\eta\le F(z)\le F(x)$, $T>0$, where $N=(h-g)^T(z-x_*)$,
$T=(h-g)^T(z-x)$, $x_*=0$. Its failure on a positive band in a neighborhood $N_0$ of zero: some
$\eta>0$ such that for every $C$ a differentiable pair in $N_0$ (eligible for $c_1=1/4$,
$c_2=1/2$) has $F_*+\eta\le F(z)\le F(x)$, $T>0$ and $N^2>CT$. The basin is
`explicit_basin` (`Local.nonradial_example`). -/
theorem RS_fails (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x))) :
    (∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < 1 / 100 →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
    ∀ N₀ ∈ 𝓝 (0 : Vec 2), ∃ η : ℝ, 0 < η ∧ ∀ C : ℝ, ∃ x z g h : Vec 2,
      x ∈ N₀ ∧ z ∈ N₀ ∧ F 0 + η ≤ F z ∧ F z ≤ F x ∧
      HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z ∧
      0 < dot (h - g) (z - x) ∧ C * dot (h - g) (z - x) < (dot (h - g) z) ^ 2 ∧
      TransportedCertificate.EligiblePair F (1 / 4) (1 / 2) x z g h :=
  BfgsCoverage.Article.Local.nonradial_example f hf F hF

/-! ### §7.1. A tame-geometric alternative (lines 392-403)

`RealAlgebraicGeometry.IsSemialgebraicObjective F` says that the graph of $F$ is
semialgebraic. -/

/-- Item `C/09_C/prose/061` (`companion/chapters/09_C.tex:394`), anchor
"Chapter~\ref{comp:A} proves that a finite convex semialgebraic function".

A finite convex semialgebraic $F:\R^n\to\R$ has finitely many affine-critical values. -/
theorem semialgebraic_values {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (hSA : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (F '' {x | AffineCriticalObjective.IsAffineCritical F x}).Finite :=
  RealAlgebraicGeometry.semialgebraic_affine_critical_values hF hSA

/-- Item `C/09_C/prose/062` (`companion/chapters/09_C.tex:394`), anchor "Its proof uses a
finite piecewise-smooth cover".

"... so the point path and its actual objective composition have simultaneous derivatives off a
finite exceptional set." For a finite convex semialgebraic $F$ and a continuous semialgebraic
point path $p$ on $[0,1]$: some finite set $E$ is such that, at every $t\in(0,1)\setminus E$,
both $p$ and $F\circ p$ are $C^\infty$ (in particular differentiable). -/
theorem path_composition_smooth {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (hSA : RealAlgebraicGeometry.IsSemialgebraicObjective F) (p : ℝ → Vec n)
    (hpc : ContinuousOn p (Icc 0 1))
    (hpS : RealAlgebraicGeometry.IsSemialgebraicCurveOn p (Icc 0 1)) :
    ∃ E : Finset ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ E → ContDiffAt ℝ ∞ p t ∧ ContDiffAt ℝ ∞ (F ∘ p) t := by
  classical
  obtain ⟨-, -, E₁, hE₁⟩ := objectiveSemialgebraicComposition n F hF hSA p hpc hpS
  obtain ⟨E₂, hE₂⟩ := semialgebraicCurveSmooth (Fin n) p (Icc 0 1) hpS
  refine ⟨E₁ ∪ E₂, fun t ht htE => ?_⟩
  rw [Finset.mem_union, not_or] at htE
  exact ⟨hE₂ t (Ioo_subset_Icc_self ht) htE.2, hE₁ t ht htE.1⟩

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/063` (`companion/chapters/09_C.tex:394`), anchor "The two-sided
supporting inequality and an affine combination".

For finite convex $F:\R^n\to\R$, a path $p$ with derivative $v$ at $t$ and $F\circ p$ with
derivative $a$ at $t$: the two-sided supporting inequality gives $g^Tv=a$ for every
$g\in\partial F(p(t))$; hence, if $p(t)$ is affine critical (an affine combination of
subgradients is zero), $a=0$. -/
theorem critical_composition_derivative_zero {n : ℕ} (F : Vec n → ℝ) (p : ℝ → Vec n) (t a : ℝ)
    (v : Vec n) (hp : HasDerivAt p v t) (hFp : HasDerivAt (F ∘ p) a t) :
    (∀ g ∈ subdifferential F (p t), dot g v = a) ∧ (IsAffineCritical F (p t) → a = 0) :=
  ⟨fun _ hg => AffineSupportPath.supporting_path_derivative_eq hg hp hFp,
    fun hc => AffineSupportPath.derivative_zero_of_affineCritical hc hp hFp⟩

/-- Item `C/09_C/prose/064` (`companion/chapters/09_C.tex:394`), anchor "Continuity joins the
resulting constants."; and Item `C/09_C/prose/067` (`companion/chapters/09_C.tex:396`),
anchor "Once finite critical values are known".

For a finite convex semialgebraic $F:\R^n\to\R$ and every piecewise-smooth path $p$ from $x$ to
$y$ in the affine-critical set, $F\circ p$ has derivative $0$ on $(0,1)$ and is constant:
$F(p(t))=F(x)$ for $t\in[0,1]$; and $F$ is constant on each piecewise-smooth path class of the
affine-critical set (its value image is a singleton). -/
theorem critical_path_values {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (hSA : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (∀ (x y : Vec n)
      (p : RealAlgebraicGeometry.PiecewiseSmoothPath {z | AffineCriticalObjective.IsAffineCritical F z}
        x y), (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun u => F (p.curve u)) 0 t) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, F (p.curve t) = F x) ∧
      ∀ x : Fin n → ℝ, ∀ q ∈ RealAlgebraicGeometry.piecewiseSmoothComponent
          {z | AffineCriticalObjective.IsAffineCritical F z} x,
        ∀ q' ∈ RealAlgebraicGeometry.piecewiseSmoothComponent
          {z | AffineCriticalObjective.IsAffineCritical F z} x, F q = F q' := by
  obtain ⟨-, hcomp⟩ := RealAlgebraicGeometry.semialgebraic_affine_critical_smooth_components hF hSA
  exact ⟨fun x y p => ⟨fun t ht =>
      RealAlgebraicGeometry.semialgebraic_affine_critical_path_hasDerivAt_zero hF hSA p ht,
    RealAlgebraicGeometry.semialgebraic_affine_critical_path_constant hF hSA p⟩,
    fun x => (hcomp x).2.2⟩

/-- Item `C/09_C/prose/066` (`companion/chapters/09_C.tex:396`), anchor "The actual
affine-critical set also has finitely many piecewise-smooth path classes".

For a finite convex semialgebraic $F:\R^n\to\R$, the affine-critical set has finitely many
piecewise-smooth path classes, each semialgebraic and piecewise-smoothly connected. -/
theorem critical_path_classes {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (hSA : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (RealAlgebraicGeometry.piecewiseSmoothComponent
        {z | AffineCriticalObjective.IsAffineCritical F z} ''
      {z | AffineCriticalObjective.IsAffineCritical F z}).Finite ∧
    ∀ x : Fin n → ℝ, RealAlgebraicGeometry.IsSemialgebraic
        (RealAlgebraicGeometry.piecewiseSmoothComponent
          {z | AffineCriticalObjective.IsAffineCritical F z} x) ∧
      RealAlgebraicGeometry.PiecewiseSmoothConnected
        (RealAlgebraicGeometry.piecewiseSmoothComponent
          {z | AffineCriticalObjective.IsAffineCritical F z} x) := by
  obtain ⟨hfin, hcomp⟩ :=
    RealAlgebraicGeometry.semialgebraic_affine_critical_smooth_components hF hSA
  exact ⟨hfin, fun x => ⟨(hcomp x).1, (hcomp x).2.1⟩⟩

/-- Item `C/09_C/prose/069` (`companion/chapters/09_C.tex:396`), anchor "These path classes
are distinguished from ordinary topological connected components".

For a semialgebraic $F$, the ordinary connected components of the affine-critical set are finitely
many and semialgebraic; if $F$ is also finite and convex, $F$ is constant on each of them. -/
theorem critical_components {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (hSA : RealAlgebraicGeometry.IsSemialgebraicObjective F) :
    (connectedComponentIn {x | AffineCriticalObjective.IsAffineCritical F x} ''
        {x | AffineCriticalObjective.IsAffineCritical F x}).Finite ∧
      (∀ p : Fin n → ℝ, RealAlgebraicGeometry.IsSemialgebraic
        (connectedComponentIn {x | AffineCriticalObjective.IsAffineCritical F x} p)) ∧
      ∀ x p q : Vec n,
        p ∈ connectedComponentIn {z | AffineCriticalObjective.IsAffineCritical F z} x →
        q ∈ connectedComponentIn {z | AffineCriticalObjective.IsAffineCritical F z} x → F p = F q :=
  ⟨(RealAlgebraicGeometry.semialgebraic_affine_critical_components hSA).1,
    (RealAlgebraicGeometry.semialgebraic_affine_critical_components hSA).2,
    fun _ _ _ hp hq => RealAlgebraicGeometry.semialgebraic_affine_critical_component_constant hF hSA
      hp hq⟩

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/070` (`companion/chapters/09_C.tex:398`), anchor "On a compact
structural sublevel above an attained minimum"; and Item `C/09_C/prose/117`
(`companion/chapters/09_C.tex:398`), corrected on 15 October 2026 (M20; before "Combining A's
low affine-critical gap with Theorem~\ref{C:thm:cluster}", where "A" was the source note's name
for Chapter 8): "Combining the low affine-critical gap of Proposition~\ref{A:semialgebraic} with
Theorem~\ref{C:thm:cluster} gives the following restricted planar basin conclusion."

For a finite convex semialgebraic $F:\R^2\to\R$ with an attained minimum ($x_*$ a minimizer): the
low affine-critical gap of Proposition `A:semialgebraic` (some $\varepsilon>0$: every
affine-critical point with $F(p)<F_*+\varepsilon$ is stationary); and, combining it with Theorem
`C:thm:cluster`, on a compact structural sublevel $\{F\le b\}$,
$b>F_*$, with strictly convex positive sublevels ($F_*<t\le b$) and the regular smooth/two-branch
hypothesis away from affine criticality (TeX form): some $\varepsilon>0$, chosen before the run,
gives for every admissible run with $F(x_0)\le F_*+\varepsilon$ convergence in value, in
distance to the full minimizer set (also Euclidean), and, under uniqueness, of the whole
sequence. -/
theorem semialgebraic_low_basin (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F)
    (hSA : RealAlgebraicGeometry.IsSemialgebraicObjective F) (xstar : Vec 2)
    (hmin : ∀ z, F xstar ≤ F z) (b : ℝ) (hb : F xstar < b) (hK : IsCompact {x | F x ≤ b})
    (hstrict : ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y)
    (hreg : ∀ p, F p ≤ b → ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ p : Vec 2, F p < F xstar + ε → IsAffineCritical F p →
      (0 : Vec 2) ∈ subdifferential F p) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) ≤ F xstar + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
        Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
        ((∀ z, F z = F xstar → z = xstar) → Tendsto R.x atTop (𝓝 xstar)) :=
  ⟨RealAlgebraicGeometry.semialgebraic_low_affine_critical_gap hF hSA xstar hmin,
    RealAlgebraicGeometry.semialgebraic_planar_low_basin hF hSA xstar hmin hb hK hstrict
      (fun p hp hn => BfgsCoverage.Article.Local.regular_of_paper (hreg p hp hn))⟩

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/071` (`companion/chapters/09_C.tex:398`), anchor "Alternatively, with
a unique minimizer and the structural hypotheses on a neighborhood".

For a finite convex semialgebraic $F:\R^2\to\R$ with a unique minimizer $x_*$, the regular
smooth/two-branch hypothesis away from affine criticality on an open neighborhood $\Omega$ of
$x_*$ and strictly convex low positive sublevels: some $\varepsilon>0$, chosen before the run,
gives $F(x_k)\to F_*$ and $x_k\to x_*$ for every admissible run with $F(x_0)<F_*+\varepsilon$
(localization traps the iterates in a low compact sublevel). -/
theorem semialgebraic_local_basin (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F)
    (hSA : RealAlgebraicGeometry.IsSemialgebraicObjective F) (xstar : Vec 2)
    (hmin : ∀ z, F xstar ≤ F z) (huniq : ∀ z, F z = F xstar → z = xstar)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (hxΩ : xstar ∈ Ω)
    (hreg : ∀ p ∈ Ω, ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (b : ℝ) (hb : F xstar < b)
    (hstrict : ∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun 2 F, F (R.x 0) < F xstar + ε →
      Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) :=
  RealAlgebraicGeometry.semialgebraic_planar_local_basin hF hSA xstar hmin huniq hΩ hxΩ
    (fun p hp hn => BfgsCoverage.Article.Local.regular_of_paper (hreg p hp hn)) hb hstrict

/-! ### §9. What can already be proved in any dimension (lines 461-496)

Statements are for $F:\R^n\to\R$ (`Vec n`), with a finite maximum representation near $p$
written `ConvexSubdifferential.LocalFiniteMax F f p` ($F(z)$ is the largest $f_i(z)$ for $z$
near $p$); "active at $p$" is $f_i(p)=F(p)$. -/

open ConvexSubdifferential in
/-- Item `C/09_C/prose/083` (`companion/chapters/09_C.tex:463`), anchor "Nearby inactive
branches can be removed by their strict gaps."

If $F$ is finite and convex, $F=\max_if_i$ near $p$ with branches $C^2$ at $p$: every branch
inactive at $p$ ($f_i(p)<F(p)$) stays inactive near $p$, so near $p$ the active set is contained
in the fixed family $J=I(p)$. -/
theorem inactive_removed {n m : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (f : Fin m → Vec n → ℝ) (p : Vec n) (hrep : LocalFiniteMax F f p)
    (hC2 : ∀ j, ContDiffAt ℝ 2 (f j) p) :
    (∀ i, f i p < F p → ∀ᶠ x in 𝓝 p, f i x < F x) ∧
      ∀ᶠ x in 𝓝 p, activeIndices F f x ⊆ activeIndices F f p := by
  have hFc : ContinuousAt F p := (convex_continuous hF).continuousAt
  have hfc : ∀ j, ContinuousAt (f j) p := fun j => (hC2 j).continuousAt
  exact ⟨fun i hi => (hfc i).eventually_lt hFc hi,
    activeIndices_eventually_subset hFc hfc hrep⟩

open ConvexSubdifferential in
/-- Item `C/09_C/prose/084` (`companion/chapters/09_C.tex:463`), anchor "Affine independence
of the family at $p$ is a sufficient condition for this local rank hypothesis."

If $F=\max_if_i$ near $p$ with branches $C^2$ at $p$ and the gradients of the family $J=I(p)$
active at $p$ (enumerated by `activeIndexMap`) are affinely independent, then the
gradient-difference matrix of the fixed family has constant rank near $p$
(`ConstantRankFields.LocallyConstantActiveRank`). -/
theorem affine_independence_sufficient {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (p : Vec n) (hrep : LocalFiniteMax F f p) (hC2 : ∀ j, ContDiffAt ℝ 2 (f j) p)
    (hind : AffineIndependent ℝ fun j => coordinateGradient (f (activeIndexMap F f p j)) p) :
    ConstantRankFields.LocallyConstantActiveRank F f p :=
  ConstantRankFields.active_affineIndependent_implies_locallyConstantActiveRank hrep hC2 hind

open AffineCriticalObjective ConvexSubdifferential in
/-- Item `C/09_C/prose/085` (`companion/chapters/09_C.tex:463`), anchor "The noncritical
restriction on $K$ is essential".

"Unit pairing with all subgradients is impossible at an affine-critical point": for finite convex
$F:\R^n\to\R$, if $p$ is affine critical, no $v$ has $g^Tv=1$ for every $g\in\partial F(p)$. -/
theorem no_unit_pairing_at_affine_critical {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (p : Vec n) (hc : IsAffineCritical F p) :
    ¬ ∃ v : Vec n, ∀ g ∈ subdifferential F p, dot g v = 1 := by
  rintro ⟨v, hv⟩
  apply (equal_rate_exists_iff_not_affineCritical hF p).mp _ hc
  refine ⟨-v, fun g hg => ?_⟩
  have h : dot g (-v) = -dot g v := by simp [dot]
  rw [h, hv g hg]

open AffineCriticalGeometry in
/-- Item `C/09_C/prose/086` (`companion/chapters/09_C.tex:465`), anchor "The minimum-norm
point $a_J(x)$ of the affine hull of these gradients is $C^1$".

For a fixed family of gradients $g_j(x)=\nabla f_j(x)$, $j\in J$ (`g x j`), that are $C^1$ at
$p$ (the branches are $C^2$), whose difference matrix has constant rank near $p$ and whose
affine hull at $p$ does not contain $0$: the point
$a_J(x)$ = `closestAffinePoint` of the family is, at every $x$, the minimum-norm point of the
affine hull ($a_J(x)$ lies in it and $\norm{a_J(x)}\le\norm z$ for all $z$ in it); $a_J$ is $C^1$
at $p$ and nonzero near $p$. -/
theorem min_norm_C1 {d n m : ℕ} (g : Vec d → Fin m → Vec n) (p : Vec d) (i : Fin m)
    (hc : ∀ j, ContDiffAt ℝ 1 (fun x => g x j) p)
    (hrank : ∀ᶠ x in 𝓝 p, (ConstantRankFields.differenceMatrix (g x) i).rank =
      (ConstantRankFields.differenceMatrix (g p) i).rank)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉
      affineSpan ℝ (Set.range fun j => euclideanVector (g p j))) :
    (∀ x, closestAffinePoint (fun j => euclideanVector (g x j)) i ∈
        affineSpan ℝ (Set.range fun j => euclideanVector (g x j)) ∧
      ∀ z ∈ affineSpan ℝ (Set.range fun j => euclideanVector (g x j)),
        ‖closestAffinePoint (fun j => euclideanVector (g x j)) i‖ ≤ ‖z‖) ∧
    ContDiffAt ℝ 1 (fun x => closestAffinePoint (fun j => euclideanVector (g x j)) i) p ∧
    ∀ᶠ x in 𝓝 p, closestAffinePoint (fun j => euclideanVector (g x j)) i ≠ 0 := by
  have hC := ConstantRankFields.closest_contDiffAt_of_constant_rank g p i hc hrank
  have hne : closestAffinePoint (fun j => euclideanVector (g p j)) i ≠ 0 :=
    fun he => hzero ((closestAffinePoint_zero_iff _ i).mp he)
  refine ⟨fun x => ⟨closestAffinePoint_mem_affineSpan _ i,
    fun z hz => (closestAffinePoint_unique_minimum _ i z hz).1⟩, hC, ?_⟩
  exact hC.continuousAt.eventually_ne hne

/-- The real power $x\mapsto x^{1/2}$ (`Real.rpow`, zero for $x<0$) is not differentiable at
$0$: its right difference quotients $1/\sqrt t$ are unbounded. -/
theorem rpow_half_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ (fun x : ℝ => x ^ (1 / 2 : ℝ)) 0 := by
  intro hd
  have hs := hd.hasDerivAt.tendsto_slope_zero_right
  set c := deriv (fun x : ℝ => x ^ (1 / 2 : ℝ)) 0
  set M := max (c + 1) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • ((0 + t) ^ (1 / 2 : ℝ) - (0 : ℝ) ^ (1 / 2 : ℝ)) < M :=
    hs (Iio_mem_nhds (lt_of_lt_of_le (lt_add_one c) (le_max_left _ _)))
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (1 / M ^ 2) :=
    Ioo_mem_nhdsGT (by positivity)
  obtain ⟨t, h1, h2⟩ := (hev.and hsmall).exists
  simp only [zero_add, smul_eq_mul] at h1
  rw [Real.zero_rpow (by norm_num), sub_zero, ← Real.sqrt_eq_rpow] at h1
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr h2.1
  have ht : Real.sqrt t ^ 2 = t := Real.sq_sqrt h2.1.le
  have hinv : t⁻¹ * Real.sqrt t = (Real.sqrt t)⁻¹ := by
    rw [← ht]
    field_simp
    ring
  rw [hinv] at h1
  have hlt : Real.sqrt t * M < 1 := by
    have h3 : t * M ^ 2 < 1 := by
      have := h2.2
      rw [lt_div_iff₀ (by positivity)] at this
      exact this
    nlinarith [sq_nonneg (Real.sqrt t * M), mul_pos hst (lt_of_lt_of_le one_pos hM1)]
  have h4 : 1 < Real.sqrt t * M := by
    have h5 := mul_lt_mul_of_pos_left h1 hst
    rw [mul_inv_cancel₀ hst.ne'] at h5
    exact h5
  linarith

/-- Item `C/09_C/prose/088` (`companion/chapters/09_C.tex:465`), anchor "No $C^\infty$
conclusion follows from $C^2$ branch data alone."

$C^2$ branch data do not give more than $C^1$ regularity of the minimum-norm point: for the
convex $C^2$ branch $f(x)=x+x^{5/2}$ on $\R$ (real power, zero for $x\le0$), the fixed family
$J=\{f\}$ has the single gradient $f'(x)$, which is therefore its minimum-norm point $a_J(x)$;
$f'(0)=1\ne0$ (the point is not affine critical), and $f'$ is $C^1$ but not $C^2$ at $0$, so in
particular not $C^\infty$. -/
theorem no_smooth_conclusion :
    ∃ f : ℝ → ℝ, ConvexOn ℝ univ f ∧ ContDiff ℝ 2 f ∧ deriv f 0 ≠ 0 ∧
      ContDiff ℝ 1 (deriv f) ∧ ¬ ContDiffAt ℝ 2 (deriv f) 0 := by
  set f : ℝ → ℝ := fun x => x + x ^ (5 / 2 : ℝ) with hfdef
  have hderiv : ∀ x, HasDerivAt f (1 + 5 / 2 * x ^ (3 / 2 : ℝ)) x := by
    intro x
    have h := (hasDerivAt_id x).add (Real.hasDerivAt_rpow_const (x := x) (p := 5 / 2)
      (Or.inr (by norm_num)))
    convert h using 1
    norm_num
  have hdf : deriv f = fun x => 1 + 5 / 2 * x ^ (3 / 2 : ℝ) := funext fun x => (hderiv x).deriv
  have hC2 : ContDiff ℝ 2 f := by
    have h := Real.contDiff_rpow_const_of_le (n := 2) (p := 5 / 2) (by norm_num)
    exact contDiff_id.add (by exact_mod_cast h)
  have hd2 : ∀ x, HasDerivAt (deriv f) (5 / 2 * (3 / 2 * x ^ (1 / 2 : ℝ))) x := by
    intro x
    rw [hdf]
    have h := ((Real.hasDerivAt_rpow_const (x := x) (p := 3 / 2) (Or.inr (by norm_num))).const_mul
      (5 / 2 : ℝ)).const_add 1
    convert h using 2
    norm_num
  have hhalf : ∀ x : ℝ, 0 ≤ x ^ (1 / 2 : ℝ) := by
    intro x
    rcases le_or_lt 0 x with hx | hx
    · exact Real.rpow_nonneg hx _
    · rw [Real.rpow_def_of_neg hx]
      have : Real.cos (1 / 2 * Real.pi) = 0 := by
        rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring, Real.cos_pi_div_two]
      rw [this, mul_zero]
  refine ⟨f, ?_, hC2, ?_, ?_, ?_⟩
  · apply convexOn_of_deriv2_nonneg convex_univ hC2.continuous.continuousOn
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt)
      (fun x _ => (hd2 x).differentiableAt.differentiableWithinAt)
    intro x _
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, (hd2 x).deriv]
    have := hhalf x
    positivity
  · rw [hdf]
    norm_num
  · have h : ContDiff ℝ (1 + 1) f := by simpa using hC2
    exact (contDiff_succ_iff_deriv.mp h).2.2
  · intro h2
    have hq : ContDiffAt ℝ 2 (fun x : ℝ => x ^ (3 / 2 : ℝ)) 0 := by
      have h := (h2.sub (contDiffAt_const (c := (1 : ℝ)))).const_smul (2 / 5 : ℝ)
      apply h.congr_of_eventuallyEq
      refine Eventually.of_forall fun x => ?_
      simp only [hdf, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨u, hu, hqu⟩ := hq.contDiffOn (m := 2) le_rfl (by simp)
    obtain ⟨s, hsu, hso, h0s⟩ := mem_nhds_iff.mp hu
    have hds : ContDiffOn ℝ 1 (deriv fun x : ℝ => x ^ (3 / 2 : ℝ)) s :=
      (hqu.mono hsu).deriv_of_isOpen hso (by norm_num)
    have hdiff : DifferentiableAt ℝ (deriv fun x : ℝ => x ^ (3 / 2 : ℝ)) 0 :=
      (hds.differentiableOn le_rfl 0 h0s).differentiableAt (hso.mem_nhds h0s)
    have hdq : (deriv fun x : ℝ => x ^ (3 / 2 : ℝ)) = fun x => 3 / 2 * x ^ (1 / 2 : ℝ) := by
      funext x
      have h := Real.hasDerivAt_rpow_const (x := x) (p := 3 / 2) (Or.inr (by norm_num))
      rw [h.deriv]
      norm_num
    rw [hdq] at hdiff
    apply rpow_half_not_differentiableAt_zero
    have h3 := hdiff.const_mul (2 / 3 : ℝ)
    convert h3 using 1
    funext x
    ring

open AffineCriticalGeometry in
/-- Item `C/09_C/disp/045` (`companion/chapters/09_C.tex:466-469`): "Hence
\[ v_J(x)=a_J(x)/\norm{a_J(x)}^2,\qquad \nabla f_i(x)^Tv_J(x)=1\quad(i\in J)." \]
For a family $g_j=\nabla f_j(x)$, $j\in J$, whose affine hull does not contain $0$, with
$a=a_J(x)$ (`closestAffinePoint`) and $v=a/\norm a^2$ (variables with their definitions): $v$ is
the library's `ConstantRankFields.commonRate`, and $g_j^Tv=1$ for every member (Euclidean inner
product, which is $g_j^Tv$). -/
theorem common_rate_pairing {n m : ℕ} (g : Fin m → Vec n) (i : Fin m)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ affineSpan ℝ (Set.range fun j => euclideanVector (g j)))
    (a v : EuclideanSpace ℝ (Fin n)) (ha : a = closestAffinePoint (fun j => euclideanVector (g j)) i)
    (hv : v = (‖a‖ ^ 2)⁻¹ • a) :
    v = ConstantRankFields.commonRate g i ∧ ∀ j, @inner ℝ _ _ (euclideanVector (g j)) v = 1 := by
  have hne : closestAffinePoint (fun j => euclideanVector (g j)) i ≠ 0 :=
    fun he => hzero ((closestAffinePoint_zero_iff _ i).mp he)
  have hvc : v = ConstantRankFields.commonRate g i := by
    rw [hv, ha]
    rfl
  exact ⟨hvc, fun j => hvc ▸ ConstantRankFields.commonRate_pairing g i hne j⟩

open AffineCriticalObjective ConvexSubdifferential TransportedCertificate in
/-- Item `C/09_C/prose/089` (`companion/chapters/09_C.tex:470`), anchor "A finite
$C^\infty$ partition of unity on buffered charts yields one $C^1$ field"; and Item
`C/09_C/prose/093` (`companion/chapters/09_C.tex:479`), anchor "Thus visibility and the secant
correction can be constructed without a BFGS matrix assumption."

Let $K$ be a compact set with no affine-critical point, and let $F:\R^n\to\R$ be finite and
convex with a finite maximum representation by branches that are $C^2$ and convex on a
neighborhood of every point of $K$, the fixed active family having constant gradient-difference
rank near each point. Then there is one $C^1$ field $v$ and open $V\supseteq K$, compact
$Q\supseteq\overline V$, constants $G,\delta>0$, $C\ge0$: $\norm{v}\le G$ on $Q$, $g^Tv(x)=1$ for
every subgradient $g\in\partial F(x)$ at every $x\in Q$ (visibility), and
$(y^Tv(z))^2/t\le C$ for every eligible pair $x,z\in Q$ with $\norm{z-x}<\delta$ (secant
correction); no BFGS matrix appears. -/
theorem one_C1_field {n m : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (f : Fin m → Vec n → ℝ) (K : Set (Vec n)) (hK : IsCompact K)
    (hrep : ∀ p ∈ K, LocalFiniteMax F f p) (hC2 : ∀ p ∈ K, ∀ j, ContDiffAt ℝ 2 (f j) p)
    (hconv : ∀ p ∈ K, ∃ V : Set (Vec n), IsOpen V ∧ p ∈ V ∧ ∀ j, ConvexOn ℝ V (f j))
    (hnc : ∀ p ∈ K, ¬IsAffineCritical F p)
    (hrank : ∀ p ∈ K, ConstantRankFields.LocallyConstantActiveRank F f p)
    (c₁ c₂ : ℝ) (hc₂ : c₂ < 1) :
    ∃ v : Vec n → Vec n, ContDiff ℝ 1 v ∧ ∃ V Q : Set (Vec n),
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Q ∧ IsCompact Q ∧
      ∃ G δ C : ℝ, 0 < G ∧ 0 < δ ∧ 0 ≤ C ∧
      (∀ x ∈ Q, sqNorm (v x) ≤ G ^ 2) ∧
      (∀ x ∈ Q, ∀ g ∈ subdifferential F x, dot g (v x) = 1) ∧
      ∀ x z g h : Vec n, x ∈ Q → z ∈ Q → ‖euclideanVector (z - x)‖ < δ →
        EligiblePair F c₁ c₂ x z g h → (dot (h - g) (v z)) ^ 2 / pairCurvature x z g h ≤ C :=
  ConstantRankFields.source_eligible_common_rate hF f hK hrep hC2 hconv hnc hrank (c₁ := c₁) hc₂

open ConvexSubdifferential in
/-- Item `C/09_C/disp/046` (`companion/chapters/09_C.tex:471-473`): "If $i$ is active at $x$,
both $\nabla F(z)^Tv(z)$ and $\nabla f_i(z)^Tv(z)$ equal one. Therefore
\[ y^Tv(z)=[\nabla f_i(z)-\nabla f_i(x)]^Tv(z)." \]
For $F=\max_jf_j$ near $x$ with branches differentiable at $x$, $F$ differentiable at $x$ and
$z$ with gradients $g$ and $h$, branch $i$ active at $x$, and the two unit pairings at $z$:
$\nabla f_i(x)=g$ and the identity holds ($y=h-g$). -/
theorem secant_numerator_identity {n m : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (f : Fin m → Vec n → ℝ) (v : Vec n → Vec n) (x z g h : Vec n)
    (hrep : LocalFiniteMax F f x) (hdiff : ∀ j, DifferentiableAt ℝ (f j) x)
    (hgx : HasFDerivAt F (gradientFunctional g) x) (_hhz : HasFDerivAt F (gradientFunctional h) z)
    (i : Fin m) (hi : f i x = F x) (hz1 : dot h (v z) = 1)
    (hz2 : dot (coordinateGradient (f i) z) (v z) = 1) :
    coordinateGradient (f i) x = g ∧
      dot (h - g) (v z) = dot (coordinateGradient (f i) z - coordinateGradient (f i) x) (v z) := by
  have hg := PlanarCrossing.actual_gradient_eq_active_branch hF hrep hdiff hgx hi
  refine ⟨hg, ?_⟩
  rw [hg, dot_sub_left, dot_sub_left, hz1, hz2]

/-- The descent estimate in $\R^n$ for a gradient that is $L$-Lipschitz in the Euclidean norm on
a convex set (the $n$-dimensional form of `PlanarGeometry.descent_estimate`). -/
theorem descent_estimate_n {n : ℕ} {f : Vec n → ℝ} {V : Set (Vec n)} (hV : Convex ℝ V)
    (hdiff : ∀ u ∈ V, DifferentiableAt ℝ f u) {M : ℝ}
    (hLip : ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient f u -
      coordinateGradient f u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    {y u : Vec n} (hy : y ∈ V) (hyu : y + u ∈ V) :
    f (y + u) - f y - dot (coordinateGradient f y) u ≤ M / 2 * sqNorm u := by
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, y + τ • u ∈ V := by
    intro τ hτ
    have h := hV hy hyu (sub_nonneg.mpr hτ.2) hτ.1 (by ring : (1 - τ) + τ = 1)
    convert h using 1
    module
  let φ : ℝ → ℝ := fun τ => f (y + τ • u) - f y - τ * dot (coordinateGradient f y) u -
    M / 2 * τ ^ 2 * sqNorm u
  have hl : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => y + τ • u) u τ := by
    intro τ
    simpa only [one_smul] using ((hasDerivAt_id τ).smul_const u).const_add y
  have hderiv : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt φ
      (dot (coordinateGradient f (y + τ • u)) u - dot (coordinateGradient f y) u -
        M * τ * sqNorm u) τ := by
    intro τ hτ
    have hf := (hasFDerivAt_coordinateGradient (hdiff _ (hmem τ hτ))).comp_hasDerivAt τ (hl τ)
    have hf' : HasDerivAt (fun τ : ℝ => f (y + τ • u))
        (dot (coordinateGradient f (y + τ • u)) u) τ := by
      simpa only [gradientFunctional_apply] using hf
    have hq : HasDerivAt (fun τ : ℝ => M / 2 * τ ^ 2 * sqNorm u) (M * τ * sqNorm u) τ := by
      convert (((hasDerivAt_id τ).pow 2).const_mul (M / 2)).mul_const (sqNorm u) using 1
      simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
      ring
    convert ((hf'.sub_const (f y)).sub ((hasDerivAt_id τ).mul_const
      (dot (coordinateGradient f y) u))).sub hq using 1
    simp
  have hnonpos : ∀ τ ∈ Ico (0 : ℝ) 1, dot (coordinateGradient f (y + τ • u)) u -
      dot (coordinateGradient f y) u - M * τ * sqNorm u ≤ 0 := by
    intro τ hτ
    have hτ' := Ico_subset_Icc_self hτ
    have hcs := BfgsCoverage.Article.Local.dot_le_euclid
      (coordinateGradient f (y + τ • u) - coordinateGradient f y) u
    have hL := hLip _ (hmem τ hτ') y hy
    rw [add_sub_cancel_left, BfgsCoverage.Article.Local.euclideanVector_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hτ.1] at hL
    have hsq := BfgsCoverage.Article.Local.euclid_norm_sq u
    rw [dot_sub_left] at hcs
    have hun := norm_nonneg (euclideanVector u)
    have h1 : dot (coordinateGradient f (y + τ • u)) u - dot (coordinateGradient f y) u ≤
        M * (τ * ‖euclideanVector u‖) * ‖euclideanVector u‖ :=
      hcs.trans (mul_le_mul_of_nonneg_right hL hun)
    have he : M * (τ * ‖euclideanVector u‖) * ‖euclideanVector u‖ = M * τ * sqNorm u := by
      rw [← hsq]
      ring
    linarith
  have hcont : ContinuousOn φ (Icc 0 1) := fun τ hτ =>
    (hderiv τ hτ).continuousAt.continuousWithinAt
  have hle := BfgsCoverage.Article.PlanarGeometry.one_sided_comparison φ _ hcont
    (fun τ hτ => (hderiv τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt) hnonpos
  simp only [φ, one_smul, one_mul, one_pow, zero_smul, add_zero, zero_mul, sub_self,
    mul_zero, zero_sub, sub_zero] at hle
  linarith

open ConvexSubdifferential TransportedCertificate in
/-- Item `C/09_C/disp/047` (`companion/chapters/09_C.tex:475-478`): "The local one-sided convex
smooth estimate and the finite-max supporting gap give
\[ \norm{\nabla f_i(z)-\nabla f_i(x)}^2\le2LD_{f_i}(z,x)\le2Ly^Ts." \]
Setting (lines 470-479): the branch $f=f_i$ is convex and $C^2$ on a larger open convex chart $V$
with $\nabla f$ $L$-Lipschitz there (Euclidean norm, $L>0$); the endpoints lie in a buffer $B$
whose Euclidean $\rho$-balls lie in $V$, with $\norm{z-x}<\rho$ (sufficiently close); $f\le F$ on
$V$ with equality at $x$ ($i$ active at $x$; the finite-max supporting gap), $F$ has gradients
$g$ at $x$ and $h$ at $z$ and $\nabla f(x)=g$ (display `C/09_C/disp/046`); $D_f(z,x)=f(z)-f(x)-
\nabla f(x)^T(z-x)$, $s=z-x$, $y=h-g$. -/
theorem cocoercivity_estimate {n : ℕ} (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (f : Vec n → ℝ) (V : Set (Vec n)) (hVopen : IsOpen V) (hfconv : ConvexOn ℝ V f)
    (hfC : ContDiffOn ℝ 2 f V) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient f u -
      coordinateGradient f u')‖ ≤ L * ‖euclideanVector (u - u')‖)
    (B : Set (Vec n)) (ρ : ℝ) (hρ : 0 < ρ)
    (hBV : ∀ u ∈ B, ∀ u' : Vec n, ‖euclideanVector (u' - u)‖ < ρ → u' ∈ V)
    (x z g h : Vec n) (hx : x ∈ B) (hz : z ∈ B) (hxz : ‖euclideanVector (z - x)‖ < ρ)
    (hfle : ∀ u ∈ V, f u ≤ F u) (hfx : f x = F x)
    (_hgx : HasFDerivAt F (gradientFunctional g) x) (hhz : HasFDerivAt F (gradientFunctional h) z)
    (hgrad : coordinateGradient f x = g) (D : ℝ)
    (hD : D = f z - f x - dot (coordinateGradient f x) (z - x)) :
    sqNorm (coordinateGradient f z - coordinateGradient f x) ≤ 2 * L * D ∧
      2 * L * D ≤ 2 * L * dot (h - g) (z - x) := by
  have hBV' : ∀ u ∈ B, u ∈ V := fun u hu => hBV u hu u (by simp [euclideanVector, hρ])
  have hxV := hBV' x hx
  have hzV := hBV' z hz
  have hdiff : ∀ u ∈ V, DifferentiableAt ℝ f u := fun u hu =>
    (hfC.contDiffAt (hVopen.mem_nhds hu)).differentiableAt (by norm_num)
  set pg := coordinateGradient f x
  set qg := coordinateGradient f z
  have hstepV : z - L⁻¹ • (qg - pg) ∈ V := by
    apply hBV z hz
    have hLz := hLip z hzV x hxV
    rw [show z - L⁻¹ • (qg - pg) - z = (-L⁻¹) • (qg - pg) by module,
      BfgsCoverage.Article.Local.euclideanVector_smul, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (inv_pos.mpr hL)]
    calc L⁻¹ * ‖euclideanVector (qg - pg)‖ ≤ L⁻¹ * (L * ‖euclideanVector (z - x)‖) :=
          mul_le_mul_of_nonneg_left hLz (inv_nonneg.mpr hL.le)
      _ = ‖euclideanVector (z - x)‖ := by field_simp
      _ < ρ := hxz
  have hcoco : sqNorm (qg - pg) ≤ 2 * L * (f z - f x - dot pg (z - x)) := by
    apply CenteredSmoothSublinear.bregman_lower_of_descent f pg qg x z L hL
    · simpa only [gradientFunctional_apply] using
        CenteredSmoothSublinear.supporting_inequality_on hfconv
          (hasFDerivAt_coordinateGradient (hdiff x hxV)) hxV hstepV
    · have hd := descent_estimate_n hfconv.1 hdiff hLip hzV
        (u := -L⁻¹ • (qg - pg)) (by simpa only [neg_smul, ← sub_eq_add_neg] using hstepV)
      simpa only [neg_smul, ← sub_eq_add_neg] using hd
  refine ⟨hD ▸ hcoco, ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsupp := convex_supporting_inequality hF hhz x
  have hfz := hfle z hzV
  rw [hD, hfx, hgrad, dot_sub_left]
  have hxz' : dot h (x - z) = -dot h (z - x) := by
    rw [show x - z = -(z - x) by abel]
    simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  linarith

/-- Item `C/09_C/prose/094` (`companion/chapters/09_C.tex:481`), anchor "\textbf{What does
not follow:}".

"$C^1$ regularity of this field does not provide the projected transport needed by the BFGS
energy." For the quadratic of the warning (lines 483-492; `spatial_setup`) and every
$0<\epsilon<1/10$: the canonical common-rate field $v=\nabla F/\norm{\nabla F}^2$ is $C^\infty$
(so $C^1$) at both endpoints and pairs to one with the gradients, the pair is eligible, but the
rank-one projected transport inequality (the Loewner inequality
$\Pi_s(a\,v(x)v(x)^T-v(x+s)v(x+s)^T)\Pi_s\succeq0$, $\Pi_s=I-ss^T/s^Ts$) fails for every real
multiplier $a$. -/
theorem C1_field_without_transport (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10) :
    (∀ N : WithTop ℕ∞, ContDiffAt ℝ N SpatialQuadraticWarning.canonicalField
        SpatialQuadraticWarning.base ∧
      ContDiffAt ℝ N SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε)) ∧
    (dot (SpatialQuadraticWarning.gradient SpatialQuadraticWarning.base)
        (SpatialQuadraticWarning.canonicalField SpatialQuadraticWarning.base) = 1 ∧
      dot (SpatialQuadraticWarning.gradient (SpatialQuadraticWarning.next ε))
        (SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε)) = 1) ∧
    TransportedCertificate.EligiblePair SpatialQuadraticWarning.objective (1 / 4) (1 / 2)
      SpatialQuadraticWarning.base (SpatialQuadraticWarning.next ε)
      (SpatialQuadraticWarning.gradient SpatialQuadraticWarning.base)
      (SpatialQuadraticWarning.gradient (SpatialQuadraticWarning.next ε)) ∧
    ∀ a : ℝ, ¬(a • (TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε) *
        outer (SpatialQuadraticWarning.canonicalField SpatialQuadraticWarning.base)
          (SpatialQuadraticWarning.canonicalField SpatialQuadraticWarning.base) *
        TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε)) -
      TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε) *
        outer (SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε))
          (SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε)) *
        TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε)).PosSemidef := by
  obtain ⟨-, -, -, -, hw⟩ := spatialCanonicalWarning
  obtain ⟨helig, -, -, -, -, hsmooth, hrate, -, hfail⟩ := hw ε hε hε'
  exact ⟨fun N => hsmooth N, hrate, helig, hfail⟩

/-- Item `C/09_C/prose/097` (`companion/chapters/09_C.tex:483`), anchor "A concrete warning
uses the entirely smooth quadratic".

The objects of the warning: $F(x)=x^TQx/2$ with $Q=\operatorname{diag}(1,2,3)\succ0$
(`SpatialQuadraticWarning.objective`, `Q`), the point $x=(1,1,1)$ (`base`), and the canonical
common-rate field $v=\nabla F/\norm{\nabla F}^2$ (`canonicalField`); $F$ is entirely smooth
($C^\infty$) and convex with $\nabla F(x)=Qx$. -/
theorem spatial_setup :
    (∀ x : Vec 3, SpatialQuadraticWarning.objective x = dot x (SpatialQuadraticWarning.Q *ᵥ x) / 2) ∧
    SpatialQuadraticWarning.Q = Matrix.diagonal ![1, 2, 3] ∧ SpatialQuadraticWarning.Q.PosDef ∧
    SpatialQuadraticWarning.base = ![1, 1, 1] ∧
    (∀ N : WithTop ℕ∞, ContDiff ℝ N SpatialQuadraticWarning.objective) ∧
    ConvexOn ℝ univ SpatialQuadraticWarning.objective ∧
    (∀ x : Vec 3, HasFDerivAt SpatialQuadraticWarning.objective
      (gradientFunctional (SpatialQuadraticWarning.Q *ᵥ x)) x) ∧
    ∀ x : Vec 3, SpatialQuadraticWarning.canonicalField x =
      (sqNorm (SpatialQuadraticWarning.Q *ᵥ x))⁻¹ • (SpatialQuadraticWarning.Q *ᵥ x) := by
  obtain ⟨hQ, hconv, hsmooth, hgrad, -⟩ := spatialCanonicalWarning
  exact ⟨fun x => rfl, rfl, hQ, rfl, hsmooth, hconv, hgrad, fun x => rfl⟩

/-- Item `C/09_C/disp/048` (`companion/chapters/09_C.tex:484-486`): "Take
\[ s=(\epsilon,0,-(\epsilon+\epsilon^2)/3),\quad y=Qs." \]
The step `step ε` is this vector, and the gradient change
$\nabla F(x+s)-\nabla F(x)$ (`change ε`) equals $Qs$. -/
theorem spatial_step (ε : ℝ) :
    SpatialQuadraticWarning.step ε = ![ε, 0, -(ε + ε ^ 2) / 3] ∧
      SpatialQuadraticWarning.change ε =
        SpatialQuadraticWarning.Q *ᵥ SpatialQuadraticWarning.step ε := by
  refine ⟨rfl, ?_⟩
  show SpatialQuadraticWarning.Q *ᵥ (SpatialQuadraticWarning.base + SpatialQuadraticWarning.step ε) -
    SpatialQuadraticWarning.Q *ᵥ SpatialQuadraticWarning.base = _
  rw [Matrix.mulVec_add, add_sub_cancel_left]

/-- Item `C/09_C/disp/049` (`companion/chapters/09_C.tex:488-491`): "Then
\[ d=\epsilon^2,\quad t=\frac{\epsilon^2(\epsilon^2+2\epsilon+4)}3,\quad
   \det[g,s,y]=\frac43\epsilon^2(1+\epsilon)\ne0." \]
With $g=\nabla F(x)$, $d=-g^Ts$ (`pairDecrease`), $t=y^Ts$ (`pairCurvature`), and $[g,s,y]$ the
matrix with columns $g,s,y$ (`tripleColumns`): the formulas hold for every $\epsilon$, and the
determinant is nonzero for $\epsilon>0$. -/
theorem spatial_values (ε : ℝ) :
    TransportedCertificate.pairDecrease SpatialQuadraticWarning.base
        (SpatialQuadraticWarning.next ε)
        (SpatialQuadraticWarning.gradient SpatialQuadraticWarning.base) = ε ^ 2 ∧
      TransportedCertificate.pairCurvature SpatialQuadraticWarning.base
        (SpatialQuadraticWarning.next ε)
        (SpatialQuadraticWarning.gradient SpatialQuadraticWarning.base)
        (SpatialQuadraticWarning.gradient (SpatialQuadraticWarning.next ε)) =
        ε ^ 2 * (ε ^ 2 + 2 * ε + 4) / 3 ∧
      (SpatialQuadraticWarning.tripleColumns
        (SpatialQuadraticWarning.gradient SpatialQuadraticWarning.base)
        (SpatialQuadraticWarning.step ε) (SpatialQuadraticWarning.change ε)).det =
        4 / 3 * ε ^ 2 * (1 + ε) ∧
      (0 < ε → (SpatialQuadraticWarning.tripleColumns
        (SpatialQuadraticWarning.gradient SpatialQuadraticWarning.base)
        (SpatialQuadraticWarning.step ε) (SpatialQuadraticWarning.change ε)).det ≠ 0) :=
  ⟨SpatialQuadraticWarning.pair_decrease ε, SpatialQuadraticWarning.pair_curvature ε,
    SpatialQuadraticWarning.printed_determinant ε,
    fun hε => (SpatialQuadraticWarning.printed_determinant_pos hε).ne'⟩

/-- Items `C/09_C/prose/098` and `C/09_C/prose/099` (`companion/chapters/09_C.tex:492`),
anchors "For small positive $\epsilon$ the pair is Armijo--weak-Wolfe eligible" and "Its
rank-one projected transport therefore fails for any finite multiplier."

For $0<\epsilon<1/10$ the pair $x$, $x+s$ is eligible for $c_1=1/4$, $c_2=1/2$, but
$v(x+s)\notin\operatorname{span}\{v(x),s\}$, so no $a,b$ give $v(x+s)=av(x)+bs$; and the
rank-one projected transport inequality fails for every multiplier $a$ (as in
`C1_field_without_transport`). -/
theorem spatial_not_in_span (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10) :
    TransportedCertificate.EligiblePair SpatialQuadraticWarning.objective (1 / 4) (1 / 2)
      SpatialQuadraticWarning.base (SpatialQuadraticWarning.next ε)
      (SpatialQuadraticWarning.gradient SpatialQuadraticWarning.base)
      (SpatialQuadraticWarning.gradient (SpatialQuadraticWarning.next ε)) ∧
    SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε) ∉
      Submodule.span ℝ ({SpatialQuadraticWarning.canonicalField SpatialQuadraticWarning.base,
        SpatialQuadraticWarning.step ε} : Set (Vec 3)) ∧
    (∀ a b : ℝ, SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε) ≠
      a • SpatialQuadraticWarning.canonicalField SpatialQuadraticWarning.base +
        b • SpatialQuadraticWarning.step ε) ∧
    ∀ a : ℝ, ¬(a • (TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε) *
        outer (SpatialQuadraticWarning.canonicalField SpatialQuadraticWarning.base)
          (SpatialQuadraticWarning.canonicalField SpatialQuadraticWarning.base) *
        TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε)) -
      TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε) *
        outer (SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε))
          (SpatialQuadraticWarning.canonicalField (SpatialQuadraticWarning.next ε)) *
        TransportedCertificate.stepProjector (SpatialQuadraticWarning.step ε)).PosSemidef := by
  obtain ⟨-, -, -, -, hw⟩ := spatialCanonicalWarning
  obtain ⟨helig, -, -, -, -, -, -, hspan, hfail⟩ := hw ε hε hε'
  exact ⟨helig, hspan, SpatialQuadraticWarning.canonicalField_not_scalar_transport hε, hfail⟩

/-- Items `C/09_C/prose/100` and `C/09_C/prose/101` (`companion/chapters/09_C.tex:492`),
anchors "Another field, the radial field, works for this quadratic." and "This is not
nonexistence of all certificates or a BFGS counterexample".

For the quadratic of the warning: the radial field $x\mapsto x-x_*$ ($x_*=0$) has
$\nabla F(x)^Tx=2F(x)$, transports exactly ($x+s=x+1\cdot s$), and satisfies the radial secant
certificate (RS) on every sublevel (`HasRadialSecantBounds`); and every infinite admissible
full-BFGS run converges, $F(x_k)\to0$ and $x_k\to0$, so the example is not a BFGS
counterexample. -/
theorem radial_field_works :
    (∀ x : Vec 3, dot (SpatialQuadraticWarning.gradient x) x = 2 * SpatialQuadraticWarning.objective x) ∧
    (∀ ε : ℝ, SpatialQuadraticWarning.next ε = SpatialQuadraticWarning.base +
      SpatialQuadraticWarning.step ε) ∧
    (∀ b : ℝ, RadialCertificate.HasRadialSecantBounds SpatialQuadraticWarning.objective
      {x | SpatialQuadraticWarning.objective x ≤ b} 0) ∧
    ∀ R : AdmissibleBFGSRun 3 SpatialQuadraticWarning.objective,
      Tendsto (fun k => SpatialQuadraticWarning.objective (R.x k)) atTop (𝓝 0) ∧
        Tendsto R.x atTop (𝓝 0) :=
  spatialQuadraticRadial

/-! ### Non-vacuity

The standing assumptions above can hold. (The contradiction hypothesis of the proof of Theorem
`C:thm:cluster`, used by `contradiction_setup` and `energy_tail_inequality`, cannot hold together
with the theorem's hypotheses: that is what the proof shows, so these two statements are vacuous
by design; likewise the assumptions of `telescoped_bound` for a run starting in $K$. Their
satisfiable cores are `energy_step_inequality` and `telescoping_algebra`.) The premises of Lemma
`C:lem:steps`, including a limit level $\ell>F_*$, hold for an actual run (second example). The
"for every run" statements of §8 (`explicit_basin`, `RS_fails`), of §7.1 and of Corollaries
`C:cor:max` and `C:cor:AC` (third sentence, `cor_AC_local`), whose hypotheses hold for the
objective of §8, apply to actual runs started as close to the minimizer as one likes; the
convergence statement of `radial_field_works` applies to an actual run on the quadratic of §9
(`spatialRun`). -/

open AffineCriticalObjective in
/-- The hypotheses of Theorem `C:thm:cluster`, of Corollary `C:cor:AC` and of the §§2-3 and §6
statements hold together with an actual admissible run starting in $K$: $F(u,v)=u^2+|v|$
(`UnexcitedMetric.objective`), $F_*=0$, $b=1$, and the library's run `UnexcitedMetric.run`
(the article's example at `Local.lean`, `Coverage/Article/Local.lean:3315`). -/
example : ∃ (F : Vec 2 → ℝ) (Fstar b : ℝ) (R : AdmissibleBFGSRun 2 F),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ Fstar < b ∧ IsCompact {x | F x ≤ b} ∧
      StrictlyConvexPositiveSublevels F Fstar b ∧ RegularSwitching F b ∧
      {p | IsAffineCritical F p} ∩ {x | F x ≤ b} ⊆ argmin F ∧
      R.x 0 ∈ {x | F x ≤ b} := by
  set F := UnexcitedMetric.objective with hFdef
  have h00 : F 0 = 0 := by simp [hFdef, UnexcitedMetric.objective]
  have hmin : ∀ x, F 0 ≤ F x := fun x => by rw [h00]; exact UnexcitedMetric.objective_nonneg x
  have huniq : ∀ x, F x = F 0 → x = 0 := fun x hx => UnexcitedMetric.unique_minimum hx
  let fb : Fin 2 → Vec 2 → ℝ := ![fun x => x 0 ^ 2 + 1 * x 1, fun x => x 0 ^ 2 + -1 * x 1]
  have hfb : ∀ i, ConvexOn ℝ univ (fb i) ∧ ContDiffOn ℝ 2 (fb i) univ := by
    intro i
    fin_cases i
    · exact ⟨BfgsCoverage.Article.Local.sq_add_lin_convex 1,
        (((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).add
          (contDiff_const.mul (contDiff_apply ℝ ℝ (1 : Fin 2)))).contDiffOn⟩
    · exact ⟨BfgsCoverage.Article.Local.sq_add_lin_convex (-1),
        (((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).add
          (contDiff_const.mul (contDiff_apply ℝ ℝ (1 : Fin 2)))).contDiffOn⟩
  have hgr : ∀ p : Vec 2, (fun i => coordinateGradient (fb i) p) =
      ![![2 * p 0, 1], ![2 * p 0, -1]] := by
    intro p
    funext i
    fin_cases i
    · exact BfgsCoverage.Article.Local.coordinateGradient_sq_add_lin 1 p
    · exact BfgsCoverage.Article.Local.coordinateGradient_sq_add_lin (-1) p
  have hrep : ∀ z : Vec 2, IsGreatest (Set.range fun i => fb i z) (F z) := by
    intro z
    refine ⟨?_, ?_⟩
    · rcases le_total 0 (z 1) with h | h
      · exact ⟨0, by simp [fb, hFdef, UnexcitedMetric.objective, abs_of_nonneg h]⟩
      · exact ⟨1, by simp [fb, hFdef, UnexcitedMetric.objective, abs_of_nonpos h]⟩
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp [fb, hFdef, UnexcitedMetric.objective, le_abs_self]
      · simp [fb, hFdef, UnexcitedMetric.objective, neg_le_abs]
  have hρ : (1 / 2 : ℝ) < (1 - 1 / 4) / (1 + 1 / 4) := by norm_num
  refine ⟨F, 0, 1, UnexcitedMetric.run 1 (1 / 2) (1 / 2) (1 / 4) (1 / 2) one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hρ,
    UnexcitedMetric.objective_convex, ⟨⟨0, h00⟩, by rintro _ ⟨x, rfl⟩; exact h00 ▸ hmin x⟩,
    one_pos, Localization.sublevel_compact UnexcitedMetric.objective_convex 0 hmin huniq 1,
    fun t _ _ x y hxy => BfgsCoverage.Article.Local.unexcited_strict_contours t x y hxy,
    fun p _ hn => ?_, ?_, ?_⟩
  · apply BfgsCoverage.Article.Local.paper_of_regular
    apply PlanarMaxRegular.regular_of_finite_max_independent UnexcitedMetric.objective_convex
      isOpen_univ (mem_univ p) hfb (Eventually.of_forall hrep) _ hn
    rw [hgr p]
    apply affineIndependent_of_ne
    intro h
    have := congrFun h 1
    norm_num at this
  · rintro p ⟨hc, _⟩
    rw [BfgsCoverage.Article.Local.unexcited_affineCritical_eq_zero p hc]
    exact hmin
  · show F (UnexcitedMetric.point (UnexcitedMetric.sign 0)
      (UnexcitedMetric.radius (1 / 2) (1 / 2) 0)) ≤ 1
    rw [hFdef, UnexcitedMetric.point_value (UnexcitedMetric.sign_sq 0)
      (UnexcitedMetric.radius_pos (by norm_num) (by norm_num) 0).le]
    norm_num [UnexcitedMetric.radius]

/-- The premises of Lemma `C:lem:steps` hold for an actual run, with a limit level $\ell>F_*$:
the library's failure run (`LGlobalFailure.source_global_failure`, $\mu=1$) on the strongly
convex objective $F$ = `LQuadraticSeed.objective 1` ($\frac12\norm x^2$ plus a maximum of three
linear functions) has $F(x_k)\downarrow0$ while $F_*=-1/514$; its sublevels are compact, and
$K_0=\{F\le0\}$ is strictly convex (`strong_convexity_suffices`, $\mu=1$); so $s_k\to0$
(`steps`). Here $b=F(x_0)$. (The run converges to $0$, which is not stationary,
`LQuadraticSeed.origin_nonstationary`.) -/
example : ∃ (F : Vec 2 → ℝ) (Fstar b : ℝ) (R : AdmissibleBFGSRun 2 F) (ℓ : ℝ),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ Fstar < b ∧ IsCompact {x | F x ≤ b} ∧
      R.x 0 ∈ {x | F x ≤ b} ∧ Antitone (fun k => F (R.x k)) ∧
      Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) ∧ Fstar < ℓ ∧
      (∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ ℓ} → x = y) ∧
      Tendsto (fun k => -R.α k • (R.H k *ᵥ R.g k)) atTop (𝓝 0) := by
  obtain ⟨R, -, -, -, -, hv, hpos, -⟩ :=
    LGlobalFailure.source_global_failure (μ := 1) one_pos univ univ_mem
  have hconv : ConvexOn ℝ univ (LQuadraticSeed.objective 1) :=
    LQuadraticSeed.objective_convex zero_le_one
  have hmin : ∀ x, LQuadraticSeed.objective 1 (LQuadraticSeed.minimizer 1) ≤
      LQuadraticSeed.objective 1 x := LQuadraticSeed.objective_minimum one_pos
  have hFstar : IsLeast (Set.range (LQuadraticSeed.objective 1))
      (LQuadraticSeed.objective 1 (LQuadraticSeed.minimizer 1)) :=
    ⟨⟨_, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
  have hneg : LQuadraticSeed.objective 1 (LQuadraticSeed.minimizer 1) < 0 := by
    rw [LQuadraticSeed.minimizer_value one_pos]
    norm_num
  have hb : LQuadraticSeed.objective 1 (LQuadraticSeed.minimizer 1) <
      LQuadraticSeed.objective 1 (R.x 0) := hneg.trans (hpos 0)
  have hK : IsCompact {x | LQuadraticSeed.objective 1 x ≤ LQuadraticSeed.objective 1 (R.x 0)} :=
    LQuadraticSeed.objective_sublevels_compact one_pos _
  have hsc : ∀ x y : Vec 2, ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a + c = 1 →
      LQuadraticSeed.objective 1 (a • x + c • y) ≤
        a * LQuadraticSeed.objective 1 x + c * LQuadraticSeed.objective 1 y -
          a * c * (1 / 2 * sqNorm (x - y)) := by
    intro x y a c ha hc hac
    have hs := (LQuadraticSeed.objective_strongConvex 1).2 (mem_univ x) (mem_univ y) ha hc hac
    have hq := FixedNormal.sqNorm_convex_combination y x a
    have ha' : 1 - a = c := by linarith
    rw [ha'] at hq
    have hcomm : c • y + a • x = a • x + c • y := add_comm _ _
    rw [hcomm] at hq
    simp only [smul_eq_mul] at hs
    nlinarith
  have hseg : ∀ x y : Vec 2,
      segment ℝ x y ⊆ frontier {z | LQuadraticSeed.objective 1 z ≤ 0} → x = y :=
    strong_convexity_suffices _ hconv _ hFstar _ hb hK 1 one_pos hsc 0 hneg (hpos 0).le
  have hx0 : R.x 0 ∈ {x | LQuadraticSeed.objective 1 x ≤ LQuadraticSeed.objective 1 (R.x 0)} :=
    le_refl (LQuadraticSeed.objective 1 (R.x 0))
  exact ⟨LQuadraticSeed.objective 1, _, _, R, 0, hconv, hFstar, hb, hK, hx0,
    R.objective_antitone, hv, hneg, hseg,
    steps _ hconv _ hFstar _ hb hK R hx0 0 R.objective_antitone hv hneg hseg⟩

open AffineCriticalObjective in
/-- The standing assumptions of §§4-5 hold, with a nonsmooth point of $C$: for the objective of
§8, $F_*=0$, $C=\{p_0\}$ for a tie point $p_0$ of $f_0=f_1$, $\ell=F(p_0)$
(`PlanarGeometry.nonradial_standing`), and valid constants $c_1=1/4$, $c_2=1/2$. -/
example : ∃ (F : Vec 2 → ℝ) (Fstar : ℝ) (C : Set (Vec 2)) (ℓ c₁ c₂ : ℝ),
    ConvexOn ℝ univ F ∧ IsLeast (range F) Fstar ∧ IsCompact C ∧ C ⊆ {x | F x = ℓ} ∧
      Fstar < ℓ ∧ (∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y) ∧
      (∀ p ∈ C, ¬IsAffineCritical F p) ∧
      (∀ p ∈ C, (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
          ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
          (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
          LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) ∧
      (∃ c ∈ C, ¬DifferentiableAt ℝ F c) ∧ 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 := by
  obtain ⟨hmin, -, hcpt, hsub, hpos, hstrict, hnc, hreg⟩ :=
    BfgsCoverage.Article.PlanarGeometry.nonradial_standing
  exact ⟨PlanarQuadraticExample.objective, 0, {BfgsCoverage.Article.PlanarGeometry.pTie},
    PlanarQuadraticExample.objective BfgsCoverage.Article.PlanarGeometry.pTie, 1 / 4, 1 / 2,
    PlanarQuadraticExample.objective_convex, hmin, hcpt, hsub, hpos, hstrict, hnc, hreg,
    ⟨_, mem_singleton _, BfgsCoverage.Article.PlanarGeometry.pTie_not_differentiable⟩,
    by norm_num, by norm_num, by norm_num⟩

/-- The hypotheses of Corollary `C:cor:max` and of its Hessian replacement (with $\mu=1$) hold
for the objective of §8 with its three branches, $U=\R^2$, $I_*=\{0,1,2\}$ and weights $1/3$;
and the definitions of §8 are satisfiable. -/
example : (∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (f : Fin 3 → Vec 2 → ℝ) (U : Set (Vec 2))
    (I : Finset (Fin 3)) (lam : I → ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      IsOpen U ∧ xstar ∈ U ∧ (∀ i, ConvexOn ℝ U (f i) ∧ ContDiffOn ℝ 2 (f i) U) ∧
      (∀ x ∈ U, IsGreatest (Set.range fun i => f i x) (F x)) ∧
      (∃ b, F xstar < b ∧ ∀ t, F xstar < t → t ≤ b →
        ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      I = Finset.univ.filter (fun i => f i xstar = F xstar) ∧
      (AffineIndependent ℝ fun i : I => coordinateGradient (f i) xstar) ∧
      (∀ i, 0 < lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • coordinateGradient (f i) xstar = 0 ∧
      ∀ i ∈ I, ∀ x ∈ U, (RadialHessian.matrix (f i) x - (1 : ℝ) • (1 : Mat 2)).PosSemidef) ∧
    ∃ (f : Fin 3 → Vec 2 → ℝ) (F : Vec 2 → ℝ),
      (∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
        f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2) ∧
      ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x)) := by
  refine ⟨?_, PlanarQuadraticExample.branch, PlanarQuadraticExample.objective, fun x => ?_,
    fun x => rfl⟩
  · have hI : (Finset.univ.filter fun i : Fin 3 => PlanarQuadraticExample.branch i 0 =
        PlanarQuadraticExample.objective 0) = Finset.univ := by
      ext i; simp [PlanarQuadraticExample.initial_active i]
    have hD : PlanarQuadraticExample.denominator 0 ≠ 0 := by
      norm_num [PlanarQuadraticExample.denominator]
    have hg : ∀ i, coordinateGradient (PlanarQuadraticExample.branch i) 0 =
        PlanarQuadraticExample.gradient i 0 :=
      fun i => PlanarQuadraticExample.coordinateGradient_eq i 0
    refine ⟨PlanarQuadraticExample.objective, 0, PlanarQuadraticExample.branch, univ,
      Finset.univ.filter fun i => PlanarQuadraticExample.branch i 0 =
        PlanarQuadraticExample.objective 0, fun _ => 1 / 3,
      PlanarQuadraticExample.objective_convex, PlanarQuadraticExample.objective_minimum,
      fun x hx => PlanarQuadraticExample.objective_unique_zero x
        (by rwa [PlanarQuadraticExample.objective_zero] at hx),
      isOpen_univ, mem_univ _, fun i => ⟨(PlanarQuadraticExample.branch_convex i),
        (PlanarQuadraticExample.branch_contDiff i).contDiffOn⟩,
      fun x _ => PlanarQuadraticExample.objective_isGreatest x,
      ⟨1, by rw [PlanarQuadraticExample.objective_zero]; norm_num,
        fun t _ _ => PlanarQuadraticExample.strict_contours t⟩, rfl, ?_, fun _ => by norm_num, ?_,
      ?_, fun i _ x _ => by simpa using (PlanarQuadraticExample.branch_actual_hessian_bounds i x).1⟩
    · have h := (PlanarQuadraticExample.gradient_affineIndependent hD).comp_embedding
        (Function.Embedding.subtype fun i : Fin 3 => i ∈ Finset.univ.filter fun i =>
          PlanarQuadraticExample.branch i 0 = PlanarQuadraticExample.objective 0)
      convert h using 1
      funext i
      simp [hg]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hI]
      norm_num
    · rw [Finset.sum_coe_sort (Finset.univ.filter fun i : Fin 3 =>
        PlanarQuadraticExample.branch i 0 = PlanarQuadraticExample.objective 0)
        (fun i => (1 / 3 : ℝ) • coordinateGradient (PlanarQuadraticExample.branch i) 0), hI,
        ← Finset.smul_sum]
      simp only [hg]
      obtain ⟨g0, g1, g2⟩ := PlanarQuadraticExample.initial_gradients
      rw [Fin.sum_univ_three, g0, g1, g2]
      ext j
      fin_cases j <;> norm_num
  · refine ⟨?_, ?_, ?_⟩ <;> simp [PlanarQuadraticExample.branch]

open AffineCriticalObjective ConvexSubdifferential in
/-- The hypotheses of the third sentence of Corollary `C:cor:AC` (`cor_AC_local`) hold for the
objective of §8 with $x_*=0$, the open box $\Omega=\{|u|<1/10,\ |v|<1/10\}$ (regular switching
and \eqref{C:eq:AC} there, `Local.example_box_facts`) and $b=1$. -/
example : ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (Ω : Set (Vec 2)) (b : ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
    IsOpen Ω ∧ xstar ∈ Ω ∧
    (∀ p ∈ Ω, ¬ IsAffineCritical F p →
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) ∧
    {p | IsAffineCritical F p} ∩ Ω ⊆ argmin F ∧ F xstar < b ∧
    (∀ t, F xstar < t → t ≤ b →
      ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) := by
  have hf : ∀ x : Vec 2, PlanarQuadraticExample.branch 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      PlanarQuadraticExample.branch 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧
      PlanarQuadraticExample.branch 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2 := fun x => by
    refine ⟨?_, ?_, ?_⟩ <;> simp [PlanarQuadraticExample.branch]
  have hbox := (BfgsCoverage.Article.Local.example_box_facts PlanarQuadraticExample.branch hf
    PlanarQuadraticExample.objective fun x => rfl).2.1
  have hΩ : IsOpen {x : Vec 2 | |x 0| < 1 / 10 ∧ |x 1| < 1 / 10} :=
    (isOpen_lt (continuous_abs.comp (continuous_apply 0)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_apply 1)) continuous_const)
  refine ⟨PlanarQuadraticExample.objective, 0, {x : Vec 2 | |x 0| < 1 / 10 ∧ |x 1| < 1 / 10}, 1,
    PlanarQuadraticExample.objective_convex, PlanarQuadraticExample.objective_minimum,
    fun x hx => PlanarQuadraticExample.objective_unique_zero x
      (by rwa [PlanarQuadraticExample.objective_zero] at hx),
    hΩ, by norm_num, fun p hp hnc => ?_, fun p hp => ?_,
    by rw [PlanarQuadraticExample.objective_zero]; norm_num,
    fun t _ _ => PlanarQuadraticExample.strict_contours t⟩
  · exact BfgsCoverage.Article.Local.paper_of_regular
      ((hbox p (le_of_lt hp.1) (le_of_lt hp.2)).2.2.2.2.2.2.2 hnc)
  · have h0 := (hbox p (le_of_lt hp.2.1) (le_of_lt hp.2.2)).2.2.2.2.2.2.1 hp.1
    refine fun y => ?_
    have h := (mem_subdifferential.mp h0) y
    simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
    linarith

/-- The "for every run" statements of §8 (`explicit_basin`, the first part of `RS_fails`) and
Corollaries `C:cor:max` and `C:cor:AC` (`cor_AC_local`) for the objective of §8 apply to actual
runs: for every $H_0\succ0$, all $0<c_1<c_2<1$ and every $\varepsilon>0$ there is an infinite
admissible full-BFGS run with initial matrix $H_0$, constants $c_1$, $c_2$ and
$F(x_0)<\min\{F(0)+\varepsilon,1/100\}$, so that $x_k\to0$. It starts at $x_0=(s,0)$ with
$s=\min\{\varepsilon/4,1/1000\}$, where only $f_0$ is active
(`PlanarQuadraticExample.objective_exists_admissible_run`, from the general existence theorem
`AdmissibleRunExistence.exists_admissible_run`). -/
example (f : Fin 3 → Vec 2 → ℝ)
    (hf : ∀ x : Vec 2, f 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      f 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧ f 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2)
    (F : Vec 2 → ℝ) (hF : ∀ x, F x = max (f 0 x) (max (f 1 x) (f 2 x)))
    (H₀ : Mat 2) (hH₀ : H₀.PosDef) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : AdmissibleBFGSRun 2 F, R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
      F (R.x 0) < F 0 + ε ∧ F (R.x 0) < 1 / 100 ∧ Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨-, rfl⟩ := PlanarQuadraticExample.eq_branch_objective f hf F hF
  set s : ℝ := min (ε / 4) (1 / 1000) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by norm_num)
  have hsε : s ≤ ε / 4 := min_le_left _ _
  have hs1 : s ≤ 1 / 1000 := min_le_right _ _
  have h1 : PlanarQuadraticExample.branch 1 ![s, 0] < PlanarQuadraticExample.branch 0 ![s, 0] := by
    norm_num [PlanarQuadraticExample.branch]
    nlinarith
  have h2 : PlanarQuadraticExample.branch 2 ![s, 0] < PlanarQuadraticExample.branch 0 ![s, 0] := by
    norm_num [PlanarQuadraticExample.branch, Matrix.cons_val_two]
    nlinarith
  obtain ⟨R, hx, hH, hc1, hc2⟩ := PlanarQuadraticExample.objective_exists_admissible_run
    (PlanarQuadraticExample.winner_zero_hasGradient h1 h2).differentiableAt H₀ hH₀ hc₁ hc₁₂ hc₂
  have hval : PlanarQuadraticExample.objective ![s, 0] = s + s ^ 2 := by
    rw [PlanarQuadraticExample.winner_zero_value h1.le h2.le]
    norm_num [PlanarQuadraticExample.branch]
  have h100 : PlanarQuadraticExample.objective (R.x 0) < 1 / 100 := by
    rw [hx, hval]
    nlinarith
  refine ⟨R, hH, hc1, hc2, ?_, h100, explicit_basin f hf _ hF R h100⟩
  rw [hx, hval, PlanarQuadraticExample.objective_zero]
  nlinarith

open AffineCriticalObjective ConvexSubdifferential in
/-- The hypotheses of the §7.1 statements hold for the objective of §8. It is convex and
semialgebraic, as a maximum of three quadratic polynomials
(`RealAlgebraicGeometry.finite_polynomial_max_semialgebraic`): the hypothesis on $F$ of
`semialgebraic_values`, `path_composition_smooth`, `critical_path_values`,
`critical_path_classes` and `critical_components`. The further hypotheses of
`semialgebraic_low_basin` hold with $x_*=0$ and $b=1/100$ (the sublevel $\{F\le1/100\}$ lies in
the box of `example_box`, where the regular switching holds off $\mathcal C_{\rm aff}$), and those
of `semialgebraic_local_basin` with the open box (as for `cor_AC_local` above); by the previous
example, actual runs start in every basin. -/
example : ∃ (F : Vec 2 → ℝ) (xstar : Vec 2) (b : ℝ),
    ConvexOn ℝ univ F ∧ RealAlgebraicGeometry.IsSemialgebraicObjective F ∧
      (∀ z, F xstar ≤ F z) ∧ (∀ z, F z = F xstar → z = xstar) ∧ F xstar < b ∧
      IsCompact {x | F x ≤ b} ∧
      (∀ t, F xstar < t → t ≤ b →
        ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {z | F z ≤ t} → x = y) ∧
      (∀ p, F p ≤ b → ¬ IsAffineCritical F p →
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
          ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
          (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
          LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) := by
  have hf : ∀ x : Vec 2, PlanarQuadraticExample.branch 0 x = x 0 + x 0 ^ 2 + x 1 ^ 2 / 2 ∧
      PlanarQuadraticExample.branch 1 x = x 1 + x 0 ^ 2 / 2 + 3 * x 1 ^ 2 / 2 ∧
      PlanarQuadraticExample.branch 2 x = -x 0 - x 1 + 3 * x 0 ^ 2 / 2 + x 1 ^ 2 := fun x => by
    refine ⟨?_, ?_, ?_⟩ <;> simp [PlanarQuadraticExample.branch]
  have hboxF := BfgsCoverage.Article.Local.example_box_facts PlanarQuadraticExample.branch hf
    PlanarQuadraticExample.objective fun x => rfl
  let P : Fin 3 → MvPolynomial (Fin 2) ℝ := ![
    MvPolynomial.X 0 + MvPolynomial.X 0 ^ 2 + MvPolynomial.C (1 / 2) * MvPolynomial.X 1 ^ 2,
    MvPolynomial.X 1 + MvPolynomial.C (1 / 2) * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C (3 / 2) * MvPolynomial.X 1 ^ 2,
    -MvPolynomial.X 0 - MvPolynomial.X 1 + MvPolynomial.C (3 / 2) * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.X 1 ^ 2]
  have hP : ∀ x : Vec 2, (fun i => MvPolynomial.eval x (P i)) =
      fun i => PlanarQuadraticExample.branch i x := by
    intro x
    funext i
    fin_cases i <;> simp [P, PlanarQuadraticExample.branch] <;> ring
  have hSA : RealAlgebraicGeometry.IsSemialgebraicObjective PlanarQuadraticExample.objective :=
    RealAlgebraicGeometry.finite_polynomial_max_semialgebraic P _ fun x => by
      rw [hP x]
      exact PlanarQuadraticExample.objective_isGreatest x
  have huniq : ∀ z, PlanarQuadraticExample.objective z = PlanarQuadraticExample.objective 0 →
      z = 0 := fun z hz => PlanarQuadraticExample.objective_unique_zero z
        (by rwa [PlanarQuadraticExample.objective_zero] at hz)
  refine ⟨PlanarQuadraticExample.objective, 0, 1 / 100, PlanarQuadraticExample.objective_convex,
    hSA, PlanarQuadraticExample.objective_minimum, huniq,
    by rw [PlanarQuadraticExample.objective_zero]; norm_num,
    Localization.sublevel_compact PlanarQuadraticExample.objective_convex 0
      PlanarQuadraticExample.objective_minimum huniq _,
    fun t _ _ => PlanarQuadraticExample.strict_contours t, fun p hp hnc => ?_⟩
  obtain ⟨h0, h1⟩ := hboxF.2.2 p hp
  exact BfgsCoverage.Article.Local.paper_of_regular ((hboxF.2.1 p h0 h1).2.2.2.2.2.2.2 hnc)

open AffineCriticalObjective ConvexSubdifferential in
/-- The hypotheses of the §9 partial statement (`one_C1_field`, and with them those of
`inactive_removed` and `affine_independence_sufficient` at its points) can hold: the quadratic of
the warning, $F(x)=x^TQx/2$ with $Q=\operatorname{diag}(1,2,3)$, as a one-branch maximum $f=(F)$,
on $K=\{(1,1,1)\}$, where $\nabla F=(1,2,3)\ne0$, so that no point of $K$ is affine critical. -/
example : ∃ (F : Vec 3 → ℝ) (f : Fin 1 → Vec 3 → ℝ) (K : Set (Vec 3)),
    ConvexOn ℝ univ F ∧ IsCompact K ∧ K.Nonempty ∧ (∀ p ∈ K, LocalFiniteMax F f p) ∧
      (∀ p ∈ K, ∀ j, ContDiffAt ℝ 2 (f j) p) ∧
      (∀ p ∈ K, ∃ V : Set (Vec 3), IsOpen V ∧ p ∈ V ∧ ∀ j, ConvexOn ℝ V (f j)) ∧
      (∀ p ∈ K, ¬IsAffineCritical F p) ∧
      (∀ p ∈ K, AffineIndependent ℝ fun j => coordinateGradient (f (activeIndexMap F f p j)) p) ∧
      ∀ p ∈ K, ConstantRankFields.LocallyConstantActiveRank F f p := by
  have hrep : ∀ p ∈ ({SpatialQuadraticWarning.base} : Set (Vec 3)),
      LocalFiniteMax SpatialQuadraticWarning.objective ![SpatialQuadraticWarning.objective] p :=
    fun p _ => Eventually.of_forall fun z => ⟨⟨0, rfl⟩, by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      exact le_rfl⟩
  have hC2 : ∀ p ∈ ({SpatialQuadraticWarning.base} : Set (Vec 3)), ∀ j,
      ContDiffAt ℝ 2 ((![SpatialQuadraticWarning.objective] : Fin 1 → Vec 3 → ℝ) j) p := by
    intro p _ j
    fin_cases j
    exact SpatialQuadraticWarning.objective_contDiff.contDiffAt
  have hind : ∀ p ∈ ({SpatialQuadraticWarning.base} : Set (Vec 3)), AffineIndependent ℝ
      fun j => coordinateGradient ((![SpatialQuadraticWarning.objective] : Fin 1 → Vec 3 → ℝ)
        (activeIndexMap SpatialQuadraticWarning.objective ![SpatialQuadraticWarning.objective] p
          j)) p := by
    intro p _
    haveI : Subsingleton (Fin (activeIndices SpatialQuadraticWarning.objective
        ![SpatialQuadraticWarning.objective] p).card) :=
      Fintype.card_le_one_iff_subsingleton.mp (by
        rw [Fintype.card_fin]
        exact (Finset.card_le_univ _).trans (by simp))
    exact affineIndependent_of_subsingleton ℝ _
  refine ⟨SpatialQuadraticWarning.objective, ![SpatialQuadraticWarning.objective],
    {SpatialQuadraticWarning.base}, SpatialQuadraticWarning.objective_convex, isCompact_singleton,
    singleton_nonempty _, hrep, hC2, fun p _ => ⟨univ, isOpen_univ, mem_univ _, fun j => by
      fin_cases j
      exact SpatialQuadraticWarning.objective_convex⟩, fun p hp => ?_, hind,
    fun p hp => affine_independence_sufficient _ _ p (hrep p hp) (hC2 p hp) (hind p hp)⟩
  rw [mem_singleton_iff] at hp
  subst hp
  refine (equal_rate_exists_iff_not_affineCritical SpatialQuadraticWarning.objective_convex _).mp
    ⟨![-1, 0, 0], fun g hg => ?_⟩
  rw [subdifferential_eq_singleton_of_hasFDerivAt SpatialQuadraticWarning.objective_convex
    (SpatialQuadraticWarning.objective_hasGradient _), mem_singleton_iff] at hg
  rw [hg, SpatialQuadraticWarning.gradient_coordinates]
  simp [SpatialQuadraticWarning.base, dot, Fin.sum_univ_three]

/-- For the run on the quadratic of §9 below: the inverse BFGS update keeps
$Q^{-1}=\operatorname{diag}(1,1/2,1/3)$ on the pair $s=(1,1,1)$, $y=Qs=(1,2,3)$ (since
$Q^{-1}y=s$). -/
theorem spatial_inverseBFGS_fixed :
    inverseBFGS (Matrix.diagonal ![1, 1 / 2, 1 / 3]) ![1, 1, 1] ![1, 2, 3] =
      Matrix.diagonal ![1, 1 / 2, 1 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseBFGS, outer, dot, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.one_apply] <;> norm_num

/-- For the run on the quadratic of §9: $\nabla F(2^{-k}(1,1,1))=2^{-k}(1,2,3)$. -/
theorem spatial_gradient_scaled (k : ℕ) :
    SpatialQuadraticWarning.gradient (((1 / 2 : ℝ) ^ k) • SpatialQuadraticWarning.base) =
      ((1 / 2 : ℝ) ^ k) • ![1, 2, 3] := by
  rw [SpatialQuadraticWarning.gradient_coordinates]
  ext i
  fin_cases i <;> simp [SpatialQuadraticWarning.base] <;> ring

/-- For the run on the quadratic of §9: the step $-\frac12Q^{-1}\nabla F(x_k)$ at
$x_k=2^{-k}(1,1,1)$ is $-2^{-(k+1)}(1,1,1)$. -/
theorem spatial_step_scaled (k : ℕ) :
    bfgsStep (Matrix.diagonal ![1, 1 / 2, 1 / 3])
      (SpatialQuadraticWarning.gradient (((1 / 2 : ℝ) ^ k) • SpatialQuadraticWarning.base))
      (1 / 2) = (-(1 / 2 : ℝ) ^ (k + 1)) • ![1, 1, 1] := by
  rw [spatial_gradient_scaled]
  ext i
  fin_cases i <;> simp [bfgsStep, Matrix.mulVec_diagonal, pow_succ] <;> ring

/-- For the run on the quadratic of §9: the gradient change is $y_k=-2^{-(k+1)}(1,2,3)$. -/
theorem spatial_change_scaled (k : ℕ) :
    SpatialQuadraticWarning.gradient (((1 / 2 : ℝ) ^ (k + 1)) • SpatialQuadraticWarning.base) -
      SpatialQuadraticWarning.gradient (((1 / 2 : ℝ) ^ k) • SpatialQuadraticWarning.base) =
      (-(1 / 2 : ℝ) ^ (k + 1)) • ![1, 2, 3] := by
  rw [spatial_gradient_scaled, spatial_gradient_scaled]
  ext i
  fin_cases i <;> simp [pow_succ] <;> ring

/-- For the run on the quadratic of §9: $F(2^{-k}(1,1,1))=3\cdot4^{-k}$. -/
theorem spatial_value_scaled (k : ℕ) :
    SpatialQuadraticWarning.objective (((1 / 2 : ℝ) ^ k) • SpatialQuadraticWarning.base) =
      3 * ((1 / 2 : ℝ) ^ k) ^ 2 := by
  rw [SpatialQuadraticWarning.objective_coordinates]
  simp [SpatialQuadraticWarning.base]
  ring

/-- For the run on the quadratic of §9: the pairings of the gradients with the steps. -/
theorem spatial_dot_scaled (k j : ℕ) :
    dot (((1 / 2 : ℝ) ^ j) • (![1, 2, 3] : Vec 3)) ((-(1 / 2 : ℝ) ^ (k + 1)) • ![1, 1, 1]) =
      -6 * (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (k + 1) := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- An admissible full-BFGS run on the quadratic of §9, $F(x)=x^TQx/2$ with
$Q=\operatorname{diag}(1,2,3)$: $x_0=(1,1,1)$, $H_k=Q^{-1}$ for every $k$, $\alpha_k=1/2$ and
$(c_1,c_2)=(1/4,1/2)$, so that $x_k=2^{-k}x_0$ and $g_k=2^{-k}(1,2,3)$. The inverse update keeps
$Q^{-1}$ because $Q^{-1}y_k=s_k$ (`spatial_inverseBFGS_fixed`, scaled by
`inverseBFGS_scale_secant_pair`); Armijo holds since $c_1\le3/4$ and weak Wolfe since
$c_2\ge1/2$. -/
def spatialRun : AdmissibleBFGSRun 3 SpatialQuadraticWarning.objective where
  convex := SpatialQuadraticWarning.objective_convex
  x := fun k => ((1 / 2 : ℝ) ^ k) • SpatialQuadraticWarning.base
  H := fun _ => Matrix.diagonal ![1, 1 / 2, 1 / 3]
  g := fun k => SpatialQuadraticWarning.gradient (((1 / 2 : ℝ) ^ k) • SpatialQuadraticWarning.base)
  α := fun _ => 1 / 2
  c₁ := 1 / 4
  c₂ := 1 / 2
  c₁_pos := by norm_num
  c₁_lt_c₂ := by norm_num
  c₂_lt_one := by norm_num
  initial_posDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  alpha_pos := fun _ => by norm_num
  gradient_nonzero := fun k h => by
    rw [spatial_gradient_scaled] at h
    have h0 := congrFun h 0
    simp at h0
  hasGradient := fun k => SpatialQuadraticWarning.objective_hasGradient _
  step := fun k => by
    rw [spatial_step_scaled]
    ext i
    fin_cases i <;> simp [SpatialQuadraticWarning.base, pow_succ] <;> ring
  update := fun k => by
    rw [spatial_step_scaled, spatial_change_scaled,
      inverseBFGS_scale_secant_pair _ _ _ (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))),
      spatial_inverseBFGS_fixed]
  armijo := fun k => by
    rw [spatial_step_scaled, spatial_gradient_scaled, spatial_value_scaled, spatial_value_scaled,
      spatial_dot_scaled]
    have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
    rw [show (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k * (1 / 2) from pow_succ _ _]
    nlinarith
  weak_wolfe := fun k => by
    rw [spatial_step_scaled, spatial_gradient_scaled, spatial_gradient_scaled, spatial_dot_scaled,
      spatial_dot_scaled]
    have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
    rw [show (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k * (1 / 2) from pow_succ _ _]
    nlinarith

/-- The convergence statement of `radial_field_works` ("every admissible run converges", for the
quadratic of §9) applies to an actual run: `spatialRun` starts at $(1,1,1)$ with $H_0=Q^{-1}$ and
$(c_1,c_2)=(1/4,1/2)$, and its values and iterates converge to $0$. -/
example : ∃ R : AdmissibleBFGSRun 3 SpatialQuadraticWarning.objective,
    R.x 0 = SpatialQuadraticWarning.base ∧ R.c₁ = 1 / 4 ∧ R.c₂ = 1 / 2 ∧
      Tendsto (fun k => SpatialQuadraticWarning.objective (R.x k)) atTop (𝓝 0) ∧
      Tendsto R.x atTop (𝓝 0) :=
  ⟨spatialRun, by simp [spatialRun], rfl, rfl, radial_field_works.2.2.2 spatialRun⟩

/-- The assumptions of `telescoping_algebra` can hold: $E_k=0$, $q_k=1$, $d_k=0$, $m=C_0=1$,
$C=0$, $P_k=\bar P=1$. -/
example : ∃ (E q d P : ℕ → ℝ) (m Cd C₀ Pbar : ℝ) (K : ℕ),
    (∀ k, 0 ≤ E k) ∧ (∀ k, 0 < q k) ∧ (∀ k, 0 ≤ d k) ∧ 0 < m ∧ 0 ≤ Cd ∧ 0 ≤ C₀ ∧
      (∀ k, K ≤ k → E (k + 1) ≤ (1 + Cd * d k) * (E k - m / q k) + C₀) ∧
      P K = 1 ∧ (∀ k, K ≤ k → P (k + 1) = P k * (1 + Cd * d k)) ∧
      ∀ k, K ≤ k → P k ≤ Pbar :=
  ⟨fun _ => 0, fun _ => 1, fun _ => 0, fun _ => 1, 1, 0, 1, 1, 0, fun _ => le_rfl,
    fun _ => one_pos, fun _ => le_rfl, one_pos, le_rfl, zero_le_one, fun _ _ => by norm_num, rfl,
    fun _ _ => by norm_num, fun _ _ => le_rfl⟩

end BfgsCoverage.Companion.Ch09C
