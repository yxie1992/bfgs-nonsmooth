import BfgsVerification.ShiftedAbsAccessibility
import BfgsVerification.AccumulatingKinks
import BfgsVerification.ModuleGGeometry
import BfgsVerification.AccessibleCurvatureBridge
import BfgsVerification.FiniteSampleCertificates
import BfgsVerification.TransportedCertificateVariants
import BfgsVerification.QuadraticGaugeAlgebra
import BfgsVerification.UnexcitedMetric
import BfgsVerification.PoweredGaugeRadial
import BfgsArticle.Coverage.Article.Energy
import BfgsArticle.Coverage.Article.Global

/-!
# Lean coverage: `companion/chapters/05_G.tex`

Chapter G ("What comparison certificates express"): the transported certificate condition
(5.E), (5.V), (5.S), (5.T); Proposition 5.2.1 (exact nonexpansion normalization) and the
ellipsoid/range geometry; Proposition 5.3.1 (pointwise feasibility of (V)-(S)); Proposition
5.3.2 = `G:prop:star` (incoming-jump obstruction) and pair realizability; the tangent/normal
geometry of Section 5.4 with the example $f(x)=\frac12(x+2)^2+|x|$; Proposition 5.6.1 (exact
scalar characterization) and Proposition 5.6.2 = `G:prop:scalarconv` (scalar convergence); the
accumulating-kink objective $h$ of Section 5.7; Proposition 5.9.1 (finite samples). Register:
`editorial/lean_coverage/register/C_05_G.json` (every display, proposition and proof, and 82
prose items).

## Lean forms

* $F:\R^n\to\R$ finite convex is `F : Vec n → ℝ` with `ConvexOn ℝ univ F`; $F_*=\min F$
  attained is `IsLeast (Set.range F) Fstar`; $K=\{F\le b\}$ compact; $0<c_1<c_2<1$;
  $K_\eta$ is written out as `{x | x ∈ K ∧ F x ≥ Fstar + η}` (the library's `positiveBand`).
* "$x$ differentiable with $g=\nabla F(x)$" is `HasFDerivAt F (gradientFunctional g) x`
  (`coordinateGradient F x` is $\nabla F(x)$); eligible pairs are `EligiblePair F c₁ c₂ x z g h`
  (`eligible_iff`), $d$, $t$, $s$ written out.
* The condition (5.V)-(5.T) on one band is a library `BandCertificate F K Fstar c₁ c₂ η`
  (`condition_iff`: a total field `W : Vec n → Mat n`, PSD at the differentiable band points,
  constants $m>0$, $C$ any real, $L\ge0$, $\delta>0$); (5.V)-(5.S) alone is
  `VisibilitySecantCertificate` (`visibilitySecant_iff`); "on each positive band" is
  `∀ η > 0, K_η nonempty → Nonempty (BandCertificate …)` (the library's `HasBandCertificates`).
* $\Pi_s$ is `stepProjector s`; ranges are `LinearMap.range (W.mulVecLin)`; the ellipsoid is
  `CertificateGeometry.ellipsoid`; $\mathcal I(z)$, $\mathcal D(z)$, $\nu(z)$ are
  `PointwiseFeasibility.IncomingPoint`, `incomingPolar`, `sourceCapacity` (values in
  $[0,\infty]$, `ℝ≥0∞`).
* Section 5.4 works in `EuclideanSpace ℝ (Fin n)` (images `euclideanVector`): $N$, $U$ are
  `AccessibleJumpGeometry.jumpSpace`, `tangentSpace`; limiting gradients are
  `IsLimitingGradient`; accessible limiting jumps are `AccessibleJump` (sequences of eligible
  band pairs with both endpoints tending to $p$, $d,t\to0$) and $N_{\rm acc}$ is
  `accessibleSpan`; a "finite continuous extension to $p$" of a certificate field is a matrix
  `Wp` with `Tendsto Cert.W (𝓝[D] p) (𝓝 Wp)`, $D$ the differentiable band points.
* $f(x)=\frac12(x+2)^2+|x|$ is `ScalarCounterexamples.shiftedAbs` (on $\R$) and
  `shiftedObjective` (on $\R^1$); $h$ is `AccumulatingKinks.objective` (`coordinateObjective` on
  $\R^1$); the knot $a_j=(1/4)^j$, $j\ge1$, is the library's `knot (j - 1)` (`knot_of_index`).
* The family index $\varepsilon$ of `G:prop:star` ranges over any type with a nontrivial limit
  filter (`incoming_jump_obstruction`; $\varepsilon\downarrow0$: `incoming_jump_obstruction_pos`).

Each display inside a proof is stated under the hypotheses of its result and the objects the
proof has introduced (as variables with their defining equations: `κ`, `What` for $\widehat W$,
`v`, `C`); a hypothesis whose name starts with `_` is a standing assumption that the Lean proof
does not use.

## Items

* Chapter introduction (line 3): `sufficient_condition`, `scalar_examples_separate`.
* Section 5.1: `positiveBand_eq`, `pair_notation`, `eligible_iff`, `condition_iff`
  (`condition_iff_psd_everywhere`), `visibilitySecant_iff`; prose `armijo_wolfe_eligible`,
  `eligible_t_pos_s_ne`, `preceding_theorem`, `local_theorem`, `failures_differ` (`leftCert`).
* Section 5.2: `exact_nonexpansion_normalization`, `normalized_field`, `exp_budget_bound`;
  `ellipsoid_eq`, `support_function`, `ellipsoid_meaning`, `range_inclusion`, `range_argument`
  (`loewner_range`), `rank_one_plane`.
* Section 5.3: `incoming_iff`, `incoming_set_eq`, `nu_eq`, `empty_predecessors`,
  `polar_description`, `pointwise_characterization`, `proof_direction`, `rank_one_suffices`;
  `incoming_jump_obstruction(_pos)`, `seminorm_display`, `basis_obstruction`,
  `basis_coefficients_bounded`, `eligible_pair_first_step`, `realizing_metric`,
  `nullspaces_meet_trivially`, `psd_seminorm_triangle`.
* Section 5.4: `jumpSpace_eq`, `projections_agree`, `accessible_jump_annihilated`,
  `range_in_accessible_tangent`, `visible_accessible_projection` (`visibility_persists`),
  `accessible_span_differs`, `full_projection_ne_zero`, `projection_zero_iff_affine`,
  `affine_weaker_than_convex`, `shifted_strongly_convex`, `shiftedAbs_eq`,
  `identity_certificate`, `small_pairs_same_side`, `identity_certificate_reasons`,
  `accessible_jumps_vanish`, `limiting_gradients_at_kink`, `full_active_conclusion_fails`,
  `constants_consistency`, `active_jump_not_accessible`, `uv_geometry`, `vertex_obstruction`
  (`spanning_jumps_obstruction`, `no_vanishing_limit`; the literal implications
  `vertex_no_direction`, `spanning_jumps_no_direction` have hypotheses that can never all hold).
* Sections 5.6-5.6.1: `exact_scalar_characterization`, `small_crossing_no_certificate`,
  `scalar_convergence` (`scalar_bfgs_convergence`), `shifted_global_nonnecessity`,
  `shifted_global_nonnecessity_interior`, `two_sublevel_counterexample` (`twoCert`),
  `interior_sublevel_no_certificate`, `zero_mem_interior_iff`, `shifted_crossing_gradients`,
  `shifted_crossing_quantities`, `shifted_crossing_eligible_divergent`.
* Section 5.7: `h_def`, `series_uniform`, `h_basic`, `h_properties`, `knot_one_sided`,
  `formula_below`, `formula_above`, `h_at_knot`, `knot_crossing_gradients`,
  `knot_crossing_quantities`, `knot_crossing_eligible`, `knot_quotient`,
  `no_certificate_knot_band`, `every_neighborhood_knot`, `h_runs_converge`, `h_smoothness`,
  `local_nonnecessity`.
* Section 5.9: `finite_sample_feasible`, `sample_constant`, `finite_tests_not_existence`.

## Corrected discrepancies (15 October 2026)

* `C/05_G/prose/008` (line 59, M21): "The preceding theorem" was, in the companion, Theorem
  `R:thm:plq` of Chapter R; the sentence now names "The one-sided transported-certificate
  convergence theorem of Chapter~\ref{comp:T}" (`C/03_T/theorem/001`): `preceding_theorem`,
  `sufficient_condition`.
* `C/05_G/prose/053` (line 269, M22): "no global certificate on a sublevel containing zero" failed
  for the sublevel $\{f\le2\}=[-2,0]$, which contains zero on its boundary
  (`two_sublevel_counterexample`, `twoCert`), and left the constants $(1/4,1/2)$ implicit; it now
  reads "but, for $(c_1,c_2)=(1/4,1/2)$, no global certificate on any sublevel containing zero in
  its interior": `shifted_global_nonnecessity_interior` (`interior_sublevel_no_certificate`).
* `C/05_G/prose/063` (line 321, M23): "No certificate exists on a positive band containing this
  knot" failed when the knot lies on the boundary of the band (`knot_band_literal_counterexample`,
  `edgeCert`); it now reads "…on a positive band whose interior contains this knot
  ($b>h(a)>\eta$)": `no_certificate_knot_band`.
* Wording points W16 (line 269, "with $\epsilon>0$") and W11 (line 89, "the proof of the
  convergence theorem of Chapter~\ref{comp:T}") were applied on the same day, and W17 as in
  Chapter 3 (lines 142 and 151, "(V) and (S)"; before "(V)--(S)"; line 72 keeps "(V)--(T)", the
  range of the three conditions).

## Non-vacuity

The examples at the end show that the hypotheses can hold: the standing assumptions of Section
5.1 with a certificate on a nonempty band ($x^2/2$); `preceding_theorem` and `local_theorem`
with admissible runs (for every $\delta>0$ a run starting below $F_*+\delta$, `quadRun`);
admissible runs on $f$ and on $h$ with $(c_1,c_2)=(1/4,1/2)$ (`shiftedRun`, `kinkRun`), so the
statements about every run on these objectives are not vacuous; the hypotheses of
`scalar_convergence`; those of `G:prop:star` for $f$; those of the accessible-jump results
`disp/019`, `disp/020`, `prose/034`-`prose/036` with a nonzero accessible jump (one jump
direction), for $u^2+|v|$ with the continuous radial certificate $W(x)=xx^T$ (`uvCert`); and two
linearly independent accessible jumps at the nonoptimal vertex $(0,0)$ of $|u|+|v|+(u-1)^2$
(hypotheses of `vertex_obstruction`, `prose/050`). The literal implications
`vertex_no_direction` and `spanning_jumps_no_direction` are vacuous (the latter for $n\ge1$): a
certificate with a finite continuous extension cannot coexist with accessible jumps spanning the
space (`vertex_obstruction`, `spanning_jumps_obstruction`).
-/

noncomputable section
open scoped BigOperators Topology ENNReal
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch05G

open TransportedCertificate

/-! ### Helpers -/

/-- The scalar derivative of `F ∘ embed` at `x 0` from the gradient of `F` at `x` (dimension
one). -/
theorem scalar_derivative {F : Vec 1 → ℝ} {x g : Vec 1}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    HasDerivAt (fun t : ℝ => F (OneDimensional.embed t)) (g 0) (x 0) := by
  have hemb : HasDerivAt OneDimensional.embed (OneDimensional.embed 1) (x 0) :=
    OneDimensional.embed.hasFDerivAt.hasDerivAt
  have h := hg.comp_hasDerivAt_of_eq (x 0) hemb (OneDimensional.embed_eval x).symm
  simpa [gradientFunctional_apply, dot] using h

/-- An eligible pair has $t>0$ (for $c_2<1$). -/
theorem eligible_t_pos {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ} (hc₂ : c₂ < 1)
    {x z g h : Vec n} (hp : EligiblePair F c₁ c₂ x z g h) : 0 < pairCurvature x z g h :=
  eligible_curvature_pos hp hc₂

/-! ### Section 5.1: the precise condition under study (lines 31-65) -/

/-- Item `C/05_G/disp/001` (`companion/chapters/05_G.tex:34-36`): the positive band
\[ K_\eta=\{x\in K:F(x)\ge F_*+\eta\},\qquad \eta>0. \]
The library's `positiveBand F K Fstar η` is this set. -/
theorem positiveBand_eq {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar η : ℝ) :
    positiveBand F K Fstar η = {x | x ∈ K ∧ F x ≥ Fstar + η} := rfl

/-- Items `C/05_G/disp/002` (`companion/chapters/05_G.tex:38-40`) and `C/05_G/disp/003`
(`companion/chapters/05_G.tex:41-43`): for differentiable endpoints $x,z$,
\[ g=\nabla F(x),\quad g_z=\nabla F(z),\quad y=g_z-g,\quad s=z-x,\qquad
   d=-g^Ts,\quad \Delta=F(x)-F(z),\quad t=y^Ts. \]
"$x$ is differentiable with $g=\nabla F(x)$" is `HasFDerivAt F (gradientFunctional g) x`, and then
$g$ is the coordinate gradient `coordinateGradient F x`; the library's `pairStep`,
`pairDecrease`, `pairCurvature` are $s$, $d$, $t$ ($\Delta$ is written out). -/
theorem pair_notation {n : ℕ} (F : Vec n → ℝ) (x z g h : Vec n)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hh : HasFDerivAt F (gradientFunctional h) z) :
    coordinateGradient F x = g ∧ coordinateGradient F z = h ∧ pairStep x z = z - x ∧
      pairDecrease x z g = -dot g (z - x) ∧ pairCurvature x z g h = dot (h - g) (z - x) :=
  ⟨PointwiseFeasibility.coordinateGradient_eq hg, PointwiseFeasibility.coordinateGradient_eq hh,
    rfl, rfl, rfl⟩

/-- Item `C/05_G/disp/004` (`companion/chapters/05_G.tex:45-47`), display (5.E): a pair is
eligible when
\[ d>0,\qquad c_1d\le\Delta\le d,\qquad t\ge(1-c_2)d, \]
with the notation of displays `disp/002`, `disp/003` (both endpoints differentiable). The
library's `EligiblePair F c₁ c₂ x z g h` is exactly this. -/
theorem eligible_iff {n : ℕ} (F : Vec n → ℝ) (c₁ c₂ : ℝ) (x z g h : Vec n)
    (s y : Vec n) (hs : s = z - x) (hy : y = h - g) (d Δ t : ℝ) (hd : d = -dot g s)
    (hΔ : Δ = F x - F z) (ht : t = dot y s) :
    EligiblePair F c₁ c₂ x z g h ↔
      (HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z) ∧
        d > 0 ∧ c₁ * d ≤ Δ ∧ Δ ≤ d ∧ t ≥ (1 - c₂) * d :=
  BfgsCoverage.Article.Energy.eligiblePair_iff F c₁ c₂ x z g h s y hs hy d Δ t hd hΔ ht

/-- Item `C/05_G/prose/003` (`companion/chapters/05_G.tex:48`): "These are the necessary
endpoint inequalities of the Armijo--weak-Wolfe formulation in Xie--Wächter." For finite convex
$F$, an Armijo--weak-Wolfe step from a differentiable $x$ to a differentiable $z=x+s$ along a
descent direction ($g^Ts<0$),
\[ F(z)\le F(x)+c_1g^Ts,\qquad \nabla F(z)^Ts\ge c_2g^Ts, \]
gives an eligible pair (the bound $\Delta\le d$ is convexity); in particular every accepted pair
$(x_k,x_{k+1})$ of an admissible run is eligible for the run's constants. -/
theorem armijo_wolfe_eligible {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (c₁ c₂ : ℝ)
    (x z g h : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x)
    (hh : HasFDerivAt F (gradientFunctional h) z) (hdesc : dot g (z - x) < 0)
    (harmijo : F z ≤ F x + c₁ * dot g (z - x))
    (hwolfe : dot h (z - x) ≥ c₂ * dot g (z - x)) :
    EligiblePair F c₁ c₂ x z g h ∧
      ∀ R : AdmissibleBFGSRun n F, ∀ k,
        EligiblePair F R.c₁ R.c₂ (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1)) := by
  refine ⟨⟨hg, hh, ?_, ?_, ?_, ?_⟩, fun R k => R.accepted_pair_eligible k⟩
  · simp only [pairDecrease, pairStep]
    linarith
  · simp only [pairDecrease, pairStep]
    linarith
  · have hs := convex_supporting_inequality hF hg z
    simp only [pairDecrease, pairStep]
    linarith
  · simp only [pairDecrease, pairCurvature, pairStep]
    have he : dot (h - g) (z - x) = dot h (z - x) - dot g (z - x) := by
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [he]
    linarith

/-- Item `C/05_G/prose/004` (`companion/chapters/05_G.tex:48`): "In particular $t>0$ and
$s\ne0$." Every eligible pair (for $c_2<1$) has $t>0$ and $s=z-x\ne0$. -/
theorem eligible_t_pos_s_ne {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ} (hc₂ : c₂ < 1)
    {x z g h : Vec n} (hp : EligiblePair F c₁ c₂ x z g h) :
    dot (h - g) (z - x) > 0 ∧ z - x ≠ 0 := by
  refine ⟨eligible_t_pos hc₂ hp, fun h0 => ?_⟩
  have hd := hp.decrease_pos
  simp only [pairDecrease, pairStep, h0, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    neg_zero, lt_irrefl] at hd

/-- Item `C/05_G/disp/005` (`companion/chapters/05_G.tex:51-56`), conditions (5.V), (5.S),
(5.T), with lines 50 and 57: on the band $K_\eta$, a finite-valued PSD field $W$ and constants
$m>0$, $C<\infty$, $L\ge0$, $\delta>0$ with
\[ g_x^TW(x)g_x\ge m,\qquad y^TW(z)y\le Ct,\qquad
   \Pi_sW(z)\Pi_s\preceq(1+Ld)\Pi_sW(x)\Pi_s,\quad \Pi_s=I-ss^T/(s^Ts), \]
the last two for all eligible pairs in the band with $d\le\delta$. Such data are exactly a
library `BandCertificate F K Fstar c₁ c₂ η` (its constant `C` is any real number, "$C<\infty$").
The field is a total function constrained only at differentiable band points: no continuity or
boundedness. -/
theorem condition_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η : ℝ)
    (Kη : Set (Vec n)) (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) :
    Nonempty (BandCertificate F K Fstar c₁ c₂ η) ↔
      ∃ (W : Vec n → Mat n) (m C L δ : ℝ), 0 < m ∧ 0 ≤ L ∧ 0 < δ ∧
        (∀ x ∈ Kη, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
          dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            ((1 + L * -dot g (z - x)) • (stepProjector (z - x) * W x * stepProjector (z - x)) -
              stepProjector (z - x) * W z * stepProjector (z - x)).PosSemidef) := by
  subst hKη
  constructor
  · rintro ⟨Cert⟩
    exact ⟨Cert.W, Cert.m, Cert.C, Cert.L, Cert.δ, Cert.m_pos, Cert.L_nonneg, Cert.delta_pos,
      fun x hx hd => Cert.positive_semidefinite x hx hd,
      fun x hx g hg => Cert.visibility x hx g hg,
      fun x hx z hz g h hp hδ => Cert.secant x z g h hx hz hp hδ,
      fun x hx z hz g h hp hδ => Cert.transport x z g h hx hz hp hδ⟩
  · rintro ⟨W, m, C, L, δ, hm, hL, hδ, hpsd, hvis, hsec, htr⟩
    exact ⟨{ W := W, m := m, C := C, L := L, δ := δ, m_pos := hm, L_nonneg := hL
             delta_pos := hδ, positive_semidefinite := hpsd, visibility := hvis
             secant := fun x z g h hx hz hp hd => hsec x hx z hz g h hp hd
             transport := fun x z g h hx hz hp hd => htr x hx z hz g h hp hd }⟩

/-- The PSD requirement of condition (5.V)-(5.T) may be read at every point of $K_\eta$ ("a
finite-valued PSD field on the band") or only at its differentiable points (the library's form,
`condition_iff`): the values at nondifferentiable points never enter (V), (S), (T). -/
theorem condition_iff_psd_everywhere {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (Fstar c₁ c₂ η : ℝ) (Kη : Set (Vec n)) (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) :
    Nonempty (BandCertificate F K Fstar c₁ c₂ η) ↔
      ∃ (W : Vec n → Mat n) (m C L δ : ℝ), 0 < m ∧ 0 ≤ L ∧ 0 < δ ∧
        (∀ x ∈ Kη, (W x).PosSemidef) ∧
        (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
          dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            ((1 + L * -dot g (z - x)) • (stepProjector (z - x) * W x * stepProjector (z - x)) -
              stepProjector (z - x) * W z * stepProjector (z - x)).PosSemidef) := by
  classical
  subst hKη
  constructor
  · rintro ⟨Cert⟩
    let W : Vec n → Mat n := fun x => if DifferentiableAt ℝ F x then Cert.W x else 0
    have hW : ∀ x, DifferentiableAt ℝ F x → W x = Cert.W x := fun x hx => if_pos hx
    refine ⟨W, Cert.m, Cert.C, Cert.L, Cert.δ, Cert.m_pos, Cert.L_nonneg, Cert.delta_pos,
      fun x hx => ?_, fun x hx g hg => ?_, fun x hx z hz g h hp hδ => ?_,
      fun x hx z hz g h hp hδ => ?_⟩
    · by_cases hd : DifferentiableAt ℝ F x
      · rw [hW x hd]; exact Cert.positive_semidefinite x hx hd
      · simp only [W, if_neg hd]; exact Matrix.PosSemidef.zero
    · rw [hW x hg.differentiableAt]; exact Cert.visibility x hx g hg
    · rw [hW z hp.gradient_z.differentiableAt]; exact Cert.secant x z g h hx hz hp hδ
    · rw [hW x hp.gradient_x.differentiableAt, hW z hp.gradient_z.differentiableAt]
      exact Cert.transport x z g h hx hz hp hδ
  · rintro ⟨W, m, C, L, δ, hm, hL, hδ, hpsd, hvis, hsec, htr⟩
    exact ⟨{ W := W, m := m, C := C, L := L, δ := δ, m_pos := hm, L_nonneg := hL,
             delta_pos := hδ, positive_semidefinite := fun x hx _ => hpsd x hx,
             visibility := hvis,
             secant := fun x z g h hx hz hp hd => hsec x hx z hz g h hp hd,
             transport := fun x z g h hx hz hp hd => htr x hx z hz g h hp hd }⟩

/-- The (V)--(S) part of the condition (without transport) is the library's
`VisibilitySecantCertificate`: a PSD field and constants $m>0$, $C$, $\delta>0$ with (5.V) and
(5.S). -/
theorem visibilitySecant_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η : ℝ)
    (Kη : Set (Vec n)) (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) :
    Nonempty (VisibilitySecantCertificate F K Fstar c₁ c₂ η) ↔
      ∃ (W : Vec n → Mat n) (m C δ : ℝ), 0 < m ∧ 0 < δ ∧
        (∀ x ∈ Kη, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
          dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) := by
  subst hKη
  constructor
  · rintro ⟨B⟩
    exact ⟨B.W, B.m, B.C, B.δ, B.m_pos, B.delta_pos,
      fun x hx hd => B.positive_semidefinite x hx hd,
      fun x hx g hg => B.visibility x hx g hg,
      fun x hx z hz g h hp hδ => B.secant x z g h hx hz hp hδ⟩
  · rintro ⟨W, m, C, δ, hm, hδ, hpsd, hvis, hsec⟩
    exact ⟨{ W := W, m := m, C := C, δ := δ, m_pos := hm, delta_pos := hδ
             positive_semidefinite := hpsd, visibility := hvis
             secant := fun x z g h hx hz hp hd => hsec x hx z hz g h hp hd }⟩

/-- Item `C/05_G/prose/008` (`companion/chapters/05_G.tex:59`), corrected on 15 October 2026
(M21; before "The preceding theorem says that"): "The one-sided transported-certificate
convergence theorem of Chapter~\ref{comp:T} says that this condition implies objective
convergence for every admissible infinite full-BFGS run in $K$, and iterate convergence under
uniqueness." That theorem is `companion/chapters/03_T.tex:90` (`C/03_T/theorem/001`). Under
the standing assumptions of Section 5.1, if every nonempty positive band $K_\eta$ carries the
condition (5.V)--(5.T) (`condition_iff`), every admissible run with constants $c_1,c_2$ and
$x_0\in K$ has $F(x_k)\to F_*$, and $x_k\to x_*$ when the minimizer $x_*$ is unique. -/
theorem preceding_theorem {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (_hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1)
    (hcert : ∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
      Nonempty (BandCertificate F K Fstar c₁ c₂ η))
    (R : AdmissibleBFGSRun n F) (hR₁ : R.c₁ = c₁) (hR₂ : R.c₂ = c₂) (hx0 : R.x 0 ∈ K) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      ∀ xstar : Vec n, (∀ x, F xstar ≤ F x) → (∀ x, (∀ z, F x ≤ F z) → x = xstar) →
        Tendsto R.x atTop (𝓝 xstar) := by
  obtain ⟨xs, hxs⟩ := hFstar.1
  have hmin : ∀ x, F xs ≤ F x := fun x => hxs ▸ hFstar.2 (Set.mem_range_self x)
  subst hK_def hR₁ hR₂ hxs
  have hconv := R.transported_certificate_convergence_on_sublevel b hK xs hmin hx0 hcert
  refine ⟨hconv.1, fun xstar hxstar huniq => ?_⟩
  have hFx : F xstar = F xs := le_antisymm (hxstar xs) (hmin xstar)
  have hcert' : HasBandCertificates F {x | F x ≤ b} (F xstar) R.c₁ R.c₂ := by
    rw [hFx]; exact hcert
  exact (R.transported_certificate_convergence_on_sublevel b hK xstar hxstar hx0 hcert').2.2
    fun x hx => huniq x fun z => by rw [hx]; exact hxstar z

/-- Item `C/05_G/prose/001` (`companion/chapters/05_G.tex:3`): "The certificate is a
sufficient analytic condition." Sufficient for convergence: under the standing assumptions of
Section 5.1, if every nonempty positive band $K_\eta$ carries the condition (5.V)--(5.T)
(`condition_iff`), every admissible run with the constants $c_1,c_2$ and $x_0\in K$ has
$F(x_k)\to F_*$, and $x_k\to x_*$ when the minimizer $x_*$ is unique. This is Chapter T's
theorem (register item `C/03_T/theorem/001`), in this chapter's setting (the same statement as
`preceding_theorem`). -/
theorem sufficient_condition {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1)
    (hcert : ∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
      Nonempty (BandCertificate F K Fstar c₁ c₂ η))
    (R : AdmissibleBFGSRun n F) (hR₁ : R.c₁ = c₁) (hR₂ : R.c₂ = c₂) (hx0 : R.x 0 ∈ K) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      ∀ xstar : Vec n, (∀ x, F xstar ≤ F x) → (∀ x, (∀ z, F x ≤ F z) → x = xstar) →
        Tendsto R.x atTop (𝓝 xstar) :=
  preceding_theorem hF Fstar hFstar b K hK_def hK c₁ c₂ hc hcert R hR₁ hR₂ hx0

/-- Item `C/05_G/prose/009` (`companion/chapters/05_G.tex:59`): "A local theorem requires the
condition only near the minimizer, then uses a sufficiently low trapped sublevel." For finite
convex $F$ with unique minimizer $x_*$, a compact sublevel $\{F\le b\}$ ($b>F(x_*)$) and a
neighborhood $U$ of $x_*$: if the condition holds on the bands of $\{F\le b\}\cap U$, there is
$\delta>0$ such that every admissible run with the constants $c_1,c_2$ and
$F(x_0)\le F(x_*)+\delta$ stays in $\{F\le b\}\cap U$ and has $F(x_k)\to F(x_*)$,
$x_k\to x_*$. -/
theorem local_theorem {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) (b : ℝ)
    (hb : F xstar < b) (_hK : IsCompact {x | F x ≤ b}) (U : Set (Vec n)) (hU : U ∈ 𝓝 xstar)
    (c₁ c₂ : ℝ)
    (hcert : ∀ η : ℝ, 0 < η → {x | x ∈ {x | F x ≤ b} ∩ U ∧ F x ≥ F xstar + η}.Nonempty →
      Nonempty (BandCertificate F ({x | F x ≤ b} ∩ U) (F xstar) c₁ c₂ η)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, R.c₁ = c₁ → R.c₂ = c₂ →
      F (R.x 0) ≤ F xstar + δ →
        (∀ k, F (R.x k) ≤ b ∧ R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) :=
  local_transported_certificate_basin hF xstar hmin huniq b hb hU hcert

open ScalarCounterexamples OneDimensional in
/-- A band certificate for $f(x)=\frac12(x+2)^2+|x|$ on any region $K$ inside $\{x<0\}$, where
$f(x)=\frac12(x+1)^2+\frac32$ is a smooth quadratic: $W=I$, $m=2\eta$, $C=1$, $L=0$, $\delta=1$. -/
def leftCert (K : Set (Vec 1)) (hK : K ⊆ {x | x 0 < 0}) (c₁ c₂ η : ℝ) (hη : 0 < η) :
    BandCertificate shiftedObjective K (shiftedObjective (embed (-1))) c₁ c₂ η where
  W := fun _ => 1
  m := 2 * η
  C := 1
  L := 0
  δ := 1
  m_pos := by linarith
  L_nonneg := le_rfl
  delta_pos := one_pos
  positive_semidefinite := fun _ _ _ => Matrix.PosSemidef.one
  visibility := fun x hx g hg => by
    have hx0 : x 0 < 0 := hK hx.1
    have hgx := ShiftedAbsAccessibility.actual_gradient_neg hg hx0
    have hb := hx.2
    simp only [shiftedObjective, shiftedAbs, embed_apply, abs_of_neg hx0] at hb
    rw [scalar_energy, hgx]
    norm_num at hb ⊢
    nlinarith
  secant := fun x z g h hx hz hp _ => by
    have hx0 : x 0 < 0 := hK hx.1
    have hz0 : z 0 < 0 := hK hz.1
    have hgx := ShiftedAbsAccessibility.actual_gradient_neg hp.gradient_x hx0
    have hhz := ShiftedAbsAccessibility.actual_gradient_neg hp.gradient_z hz0
    rw [scalar_energy]
    simp only [pairCurvature, pairStep, dot, Fin.sum_univ_one, Pi.sub_apply, hgx, hhz,
      Matrix.one_apply_eq]
    nlinarith [sq_nonneg (z 0 - x 0)]
  transport := fun x z g h _ _ hp _ => by
    have hs : pairStep x z ≠ 0 := by
      intro h0
      have := hp.decrease_pos
      simp [pairDecrease, h0, dot] at this
    rw [BfgsCoverage.Article.Energy.stepProjector_one_dim hs]
    simpa using Matrix.PosSemidef.zero

open ScalarCounterexamples OneDimensional in
/-- Item `C/05_G/prose/010` (`companion/chapters/05_G.tex:59`): "Failure on a large sublevel
and failure in every neighborhood of a minimizer are different statements." For
$f(x)=\frac12(x+2)^2+|x|$ (minimizer $-1$) and $(c_1,c_2)=(1/4,1/2)$ the condition fails on
the sublevel $\{f\le3\}$, which contains the minimizer, yet it holds on $\{f\le3\}\cap U$ for a
neighborhood $U=\{x<0\}$ of the minimizer; for the accumulating-kink objective $h$ of
\eqref{G:eq:infinite} it fails on every neighborhood of its minimizer $0$. -/
theorem failures_differ :
    embed (-1) ∈ {x | shiftedObjective x ≤ 3} ∧
    ¬ HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) ∧
    (∃ U ∈ 𝓝 (embed (-1)), HasBandCertificates shiftedObjective
        ({x | shiftedObjective x ≤ 3} ∩ U) (shiftedObjective (embed (-1))) (1 / 4) (1 / 2)) ∧
    ∀ U ∈ 𝓝 (0 : Vec 1),
      ¬ HasBandCertificates AccumulatingKinks.coordinateObjective U 0 (1 / 4) (1 / 2) := by
  refine ⟨by norm_num [shiftedObjective, shiftedAbs], shifted_no_band_certificates,
    ⟨{x | x 0 < 0}, ?_, fun η hη _ => ⟨leftCert _ (fun x hx => hx.2) _ _ η hη⟩⟩,
    fun U hU => AccumulatingKinks.every_neighborhood_no_certificates hU⟩
  have hopen : IsOpen {x : Vec 1 | x 0 < 0} := isOpen_lt (continuous_apply 0) continuous_const
  exact hopen.mem_nhds (by norm_num)

/-! ### Section 5.2: the expansion allowance can be removed (lines 68-91) -/

/-- Item `C/05_G/proposition/001` (`companion/chapters/05_G.tex:71-77`), Proposition 5.2.1 (Exact
nonexpansion normalization), with display (5.T0) (`disp/006`). Under the standing assumptions
of Section 5.1, on each positive band the condition (5.V)--(5.T) (a `BandCertificate`, see
`condition_iff`) holds if and only if it holds with $L=0$:
\[ \Pi_s\widehat W(z)\Pi_s\preceq\Pi_s\widehat W(x)\Pi_s; \]
the other constants may change, but the band and the eligible pairs (with the same threshold
$\delta$) are unchanged. -/
theorem exact_nonexpansion_normalization {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η) (Kη : Set (Vec n))
    (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) :
    (Nonempty (BandCertificate F K Fstar c₁ c₂ η) ↔
      ∃ (W : Vec n → Mat n) (m C δ : ℝ), 0 < m ∧ 0 < δ ∧
        (∀ x ∈ Kη, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
          dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            (stepProjector (z - x) * W x * stepProjector (z - x) -
              stepProjector (z - x) * W z * stepProjector (z - x)).PosSemidef)) ∧
    ∀ Cert : BandCertificate F K Fstar c₁ c₂ η,
      ∃ Cert' : BandCertificate F K Fstar c₁ c₂ η, Cert'.L = 0 ∧ Cert'.δ = Cert.δ := by
  have hb : ∀ x ∈ positiveBand F K Fstar η, F x ≤ b := fun x hx => by
    have := hx.1
    rw [hK_def] at this
    exact this
  subst hKη
  refine ⟨⟨fun ⟨Cert⟩ => ?_, fun ⟨W, m, C, δ, hm, hδ, hpsd, hvis, hsec, htr⟩ => ?_⟩, fun Cert =>
    ⟨Cert.normalize hc.1 hc.2.2 b hb, Cert.normalize_budget hc.1 hc.2.2 b hb⟩⟩
  · let N := Cert.normalize hc.1 hc.2.2 b hb
    have hL : N.L = 0 := (Cert.normalize_budget hc.1 hc.2.2 b hb).1
    refine ⟨N.W, N.m, N.C, N.δ, N.m_pos, N.delta_pos,
      fun x hx hd => N.positive_semidefinite x hx hd, fun x hx g hg => N.visibility x hx g hg,
      fun x hx z hz g h hp hd => N.secant x z g h hx hz hp hd, fun x hx z hz g h hp hd => ?_⟩
    have ht := N.transport x z g h hx hz hp hd
    rw [hL, zero_mul, add_zero, one_smul] at ht
    exact ht
  · exact ⟨{ W := W, m := m, C := C, L := 0, δ := δ, m_pos := hm, L_nonneg := le_rfl,
              delta_pos := hδ, positive_semidefinite := hpsd, visibility := hvis,
              secant := fun x z g h hx hz hp hd => hsec x hx z hz g h hp hd,
              transport := fun x z g h hx hz hp hd => by
                rw [zero_mul, add_zero, one_smul]
                exact htr x hx z hz g h hp hd }⟩

/-- Item `C/05_G/disp/007` (`companion/chapters/05_G.tex:80-82`), in the proof of the
Proposition (Exact nonexpansion normalization): given a certificate (5.V)--(5.T) on $K_\eta$,
put $\kappa=L/c_1$ and
\[ \widehat W(x)=e^{\kappa(F(x)-F_*)}W(x). \]
This $\widehat W$ is the field of the library's normalized certificate `Cert.normalize`, which
satisfies (5.V), (5.S) and (5.T0) ($L=0$) with the same threshold $\delta$. -/
theorem normalized_field {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (κ : ℝ) (hκ : κ = Cert.L / c₁)
    (What : Vec n → Mat n) (hWhat : ∀ x, What x = Real.exp (κ * (F x - Fstar)) • Cert.W x) :
    ∃ Cert' : BandCertificate F K Fstar c₁ c₂ η, Cert'.W = What ∧ Cert'.L = 0 ∧
      Cert'.δ = Cert.δ := by
  have hb : ∀ x ∈ positiveBand F K Fstar η, F x ≤ b := fun x hx => by
    have := hx.1
    rw [hK_def] at this
    exact this
  refine ⟨Cert.normalize hc.1 hc.2.2 b hb, funext fun x => ?_,
    Cert.normalize_budget hc.1 hc.2.2 b hb⟩
  rw [Cert.normalize_field hc.1 hc.2.2 b hb x, hWhat x, hκ]

/-- Item `C/05_G/disp/008` (`companion/chapters/05_G.tex:84-86`), in the proof of the
Proposition (Exact nonexpansion normalization): for an eligible pair in the band with
$d\le\delta$, since $\Delta\ge c_1d$ and $\kappa=L/c_1$,
\[ e^{-\kappa\Delta}(1+Ld)\le e^{-Ld}(1+Ld)\le1. \] -/
theorem exp_budget_bound {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (κ : ℝ) (hκ : κ = Cert.L / c₁)
    (x z g h : Vec n) (_hx : x ∈ positiveBand F K Fstar η) (_hz : z ∈ positiveBand F K Fstar η)
    (hp : EligiblePair F c₁ c₂ x z g h) (_hdδ : pairDecrease x z g ≤ Cert.δ)
    (d Δ : ℝ) (hd : d = -dot g (z - x)) (hΔ : Δ = F x - F z) :
    Real.exp (-κ * Δ) * (1 + Cert.L * d) ≤ Real.exp (-Cert.L * d) * (1 + Cert.L * d) ∧
      Real.exp (-Cert.L * d) * (1 + Cert.L * d) ≤ 1 := by
  have hdpos : 0 < d := by rw [hd]; exact hp.decrease_pos
  have harm : c₁ * d ≤ Δ := by rw [hd, hΔ]; exact hp.armijo
  have hL := Cert.L_nonneg
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg hL hc.1.le
  have hκc : κ * c₁ = Cert.L := by rw [hκ]; field_simp [hc.1.ne']
  have hle : Cert.L * d ≤ κ * Δ := by
    calc Cert.L * d = κ * (c₁ * d) := by rw [← hκc]; ring
      _ ≤ κ * Δ := mul_le_mul_of_nonneg_left harm hκ0
  have hpos : 0 ≤ 1 + Cert.L * d := by nlinarith
  constructor
  · apply mul_le_mul_of_nonneg_right _ hpos
    apply Real.exp_le_exp.mpr
    linarith
  · have h1 := Real.add_one_le_exp (Cert.L * d)
    have h2 : Real.exp (-Cert.L * d) * Real.exp (Cert.L * d) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-Cert.L * d) := Real.exp_pos _
    nlinarith

/-! ### Section 5.2.1: an ellipsoid interpretation (lines 94-118) -/

/-- Item `C/05_G/disp/009` (`companion/chapters/05_G.tex:97-99`): the possibly degenerate
centered ellipsoid
\[ \mathcal E_x=W(x)^{1/2}\{v:\|v\|\le1\} \]
of a PSD matrix $W$ (Euclidean unit ball; $W^{1/2}$ the PSD square root) is the library's
`CertificateGeometry.ellipsoid hW`. -/
theorem ellipsoid_eq {n : ℕ} {W : Mat n} (hW : W.PosSemidef) :
    CertificateGeometry.ellipsoid hW = hW.sqrt.mulVec '' {v | ‖euclideanVector v‖ ≤ 1} ∧
      hW.sqrt.PosSemidef ∧ hW.sqrt * hW.sqrt = W := by
  refine ⟨?_, hW.posSemidef_sqrt, hW.sqrt_mul_self⟩
  change hW.sqrt.mulVec '' CertificateGeometry.euclideanUnitBall = _
  rw [CertificateGeometry.euclideanUnitBall_eq]
  ext v
  simp

/-- Item `C/05_G/prose/013` (`companion/chapters/05_G.tex:100`): "Its support function is
$h_{\mathcal E_x}(a)=\sqrt{a^TW(x)a}$." For every PSD $W$ and every $a$,
$\sup_{v\in\mathcal E}a^Tv=\sqrt{a^TWa}$ (the supremum is attained). -/
theorem support_function {n : ℕ} {W : Mat n} (hW : W.PosSemidef) (a : Vec n) :
    sSup ((fun v => dot a v) '' CertificateGeometry.ellipsoid hW) = Real.sqrt (dot a (W *ᵥ a)) :=
  CertificateGeometry.ellipsoid_support hW a

/-- Item `C/05_G/prose/014` (`companion/chapters/05_G.tex:100-105`): "Thus the normalized
condition means: (i) $\mathcal E_x$ contains a direction with descent magnitude at least
$\sqrt m$; (ii) every incoming gradient change has magnitude at most $\sqrt{Ct}$ when tested on
$\mathcal E_z$; (iii) $\Pi_s\mathcal E_z\subseteq\Pi_s\mathcal E_x$ for every eligible
small-decrease pair." For PSD $W(x)$, $W(z)$, a gradient $g$, a jump $y$, a step $s$ and
$m>0$: (5.V) at $x$ is (i), (5.S) for the pair is (ii), and (5.T0) for the pair is (iii). -/
theorem ellipsoid_meaning {n : ℕ} {Wx Wz : Mat n} (hWx : Wx.PosSemidef) (hWz : Wz.PosSemidef)
    (g y s : Vec n) (m C t : ℝ) (hm : 0 < m) :
    (dot g (Wx *ᵥ g) ≥ m ↔
        ∃ v ∈ CertificateGeometry.ellipsoid hWx, -dot g v ≥ Real.sqrt m) ∧
      (dot y (Wz *ᵥ y) ≤ C * t ↔
        0 ≤ C * t ∧ ∀ v ∈ CertificateGeometry.ellipsoid hWz, |dot y v| ≤ Real.sqrt (C * t)) ∧
      ((stepProjector s * Wx * stepProjector s - stepProjector s * Wz * stepProjector s).PosSemidef ↔
        (stepProjector s).mulVec '' CertificateGeometry.ellipsoid hWz ⊆
          (stepProjector s).mulVec '' CertificateGeometry.ellipsoid hWx) :=
  ⟨CertificateGeometry.ellipsoid_visibility_iff hWx g m hm.le,
    CertificateGeometry.ellipsoid_suppression_iff hWz y (C * t),
    (CertificateGeometry.step_projected_ellipsoid_subset_iff hWx hWz s).symm⟩

/-- Item `C/05_G/disp/010` (`companion/chapters/05_G.tex:109-111`), equation `G:eq:range`: the
necessary rank consequence of (5.T0),
\[ \operatorname{range}W(z)\subseteq\operatorname{range}W(x)+\operatorname{span}\{s\}. \]
For a certificate with $L=0$ (the normalized condition) and an eligible pair in the band with
$d\le\delta$; ranges are `LinearMap.range (W.mulVecLin)`. -/
theorem range_inclusion {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ}
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (hL : Cert.L = 0) (x z g h : Vec n)
    (hx : x ∈ positiveBand F K Fstar η) (hz : z ∈ positiveBand F K Fstar η)
    (hp : EligiblePair F c₁ c₂ x z g h) (hd : -dot g (z - x) ≤ Cert.δ) :
    LinearMap.range (Cert.W z).mulVecLin ≤
      LinearMap.range (Cert.W x).mulVecLin ⊔ Submodule.span ℝ {z - x} := by
  have ht := Cert.transport x z g h hx hz hp hd
  rw [hL, zero_mul, add_zero, one_smul] at ht
  exact CertificateGeometry.range_le_sup_span_of_projected_order
    (Cert.positive_semidefinite x hx hp.gradient_x.differentiableAt)
    (Cert.positive_semidefinite z hz hp.gradient_z.differentiableAt) (z - x) ht

/-- Loewner order and ranges: for PSD $A\preceq B$, $\operatorname{range}A\subseteq
\operatorname{range}B$ (the library's projected statement with $s=0$, where $\Pi_0=I$). -/
theorem loewner_range {n : ℕ} {A B : Mat n} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : (B - A).PosSemidef) :
    LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin := by
  have hP : stepProjector (0 : Vec n) = 1 := by
    simp [stepProjector, sqNorm]
  have h := CertificateGeometry.range_le_sup_span_of_projected_order hB hA 0
    (by rw [hP]; simpa using hAB)
  simpa using h

/-- Item `C/05_G/prose/017` (`companion/chapters/05_G.tex:112`): "Indeed, Loewner ordering
implies inclusion of the ranges of the projected PSD matrices. The range of $\Pi_sW\Pi_s$ is
$\Pi_s\range W$, because it equals the range of $(\Pi_sW^{1/2})(\Pi_sW^{1/2})^T$. Lifting the
projected inclusion proves \eqref{G:eq:range}." For PSD $W(x)$, $W(z)$ with (5.T0): the range of
$\Pi_sW(z)\Pi_s$ lies in that of $\Pi_sW(x)\Pi_s$; for every PSD $W$,
$\Pi_sW\Pi_s=(\Pi_sW^{1/2})(\Pi_sW^{1/2})^T$ and its range is $\Pi_s\range W$; and
\eqref{G:eq:range} follows. -/
theorem range_argument {n : ℕ} {Wx Wz : Mat n} (hWx : Wx.PosSemidef) (hWz : Wz.PosSemidef)
    (s : Vec n)
    (hT0 : (stepProjector s * Wx * stepProjector s - stepProjector s * Wz * stepProjector s).PosSemidef) :
    LinearMap.range (stepProjector s * Wz * stepProjector s).mulVecLin ≤
        LinearMap.range (stepProjector s * Wx * stepProjector s).mulVecLin ∧
      (∀ (W : Mat n) (hW : W.PosSemidef),
        stepProjector s * W * stepProjector s =
            (stepProjector s * hW.sqrt) * (stepProjector s * hW.sqrt)ᵀ ∧
          LinearMap.range (stepProjector s * W * stepProjector s).mulVecLin =
            (LinearMap.range W.mulVecLin).map (stepProjector s).mulVecLin) ∧
      LinearMap.range Wz.mulVecLin ≤ LinearMap.range Wx.mulVecLin ⊔ Submodule.span ℝ {s} := by
  have hPs : (stepProjector s)ᵀ = stepProjector s := (stepProjector_isSymm s).eq
  refine ⟨loewner_range (projected_psd hWz s) (projected_psd hWx s) hT0, fun W hW => ⟨?_, ?_⟩,
    CertificateGeometry.range_le_sup_span_of_projected_order hWx hWz s hT0⟩
  · have hs : hW.sqrtᵀ = hW.sqrt := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hW.posSemidef_sqrt.isHermitian
    rw [Matrix.transpose_mul, hs, hPs]
    calc stepProjector s * W * stepProjector s
        = stepProjector s * (hW.sqrt * hW.sqrt) * stepProjector s := by rw [hW.sqrt_mul_self]
      _ = stepProjector s * hW.sqrt * (hW.sqrt * stepProjector s) := by
          simp only [Matrix.mul_assoc]
  · have h := CertificateGeometry.projected_matrixRange hW (stepProjector s)
    rw [hPs] at h
    exact h

/-- Item `C/05_G/prose/018` (`companion/chapters/05_G.tex:112`): "For a rank-one field, a
new comparison direction must therefore lie in the plane spanned by the old comparison direction
and the step." If $W(x)=ww^T$, $W(z)=vv^T$ satisfy (5.T0) for the step $s$, then
$v\in\operatorname{span}\{w,s\}$. -/
theorem rank_one_plane {n : ℕ} (w v s : Vec n)
    (hT0 : (stepProjector s * outer w w * stepProjector s -
      stepProjector s * outer v v * stepProjector s).PosSemidef) :
    v ∈ Submodule.span ℝ ({w, s} : Set (Vec n)) :=
  CertificateGeometry.rankOne_direction_mem_plane w v s hT0

/-! ### Section 5.3: removing the matrix from pointwise feasibility (lines 121-153) -/

/-- Item `C/05_G/prose/019` (`companion/chapters/05_G.tex:124`): "For each differentiable
endpoint $z$, let $\mathcal I(z)$ be all differentiable predecessors $x$ for which $(x,z)$ is
eligible, belongs to the band, and has $d\le\delta$." The differentiable band points are the
library's `BandPoint F K Fstar η`, and $\mathcal I(z)$ is `IncomingPoint F K Fstar c₁ c₂ η δ z`
(gradients `coordinateGradient`). -/
theorem incoming_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η δ : ℝ)
    (z : PointwiseFeasibility.BandPoint F K Fstar η) (x : Vec n) :
    (z.val ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z.val) ∧
      ((∃ p : PointwiseFeasibility.IncomingPoint F K Fstar c₁ c₂ η δ z, p.val.val = x) ↔
        x ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F x ∧
          EligiblePair F c₁ c₂ x z.val (coordinateGradient F x) (coordinateGradient F z.val) ∧
          -dot (coordinateGradient F x) (z.val - x) ≤ δ) := by
  refine ⟨z.property, ⟨?_, ?_⟩⟩
  · rintro ⟨⟨⟨x', hx'⟩, hp, hd⟩, rfl⟩
    exact ⟨hx'.1, hx'.2, hp, hd⟩
  · rintro ⟨hx, hdx, hp, hd⟩
    exact ⟨⟨⟨x, hx, hdx⟩, hp, hd⟩, rfl⟩

/-- Item `C/05_G/disp/011` (`companion/chapters/05_G.tex:125-128`): the set
\[ \mathcal D(z)=\Bigl\{v:\bigl|[\nabla F(z)-\nabla F(x)]^Tv\bigr|\le\sqrt{t(x,z)}
   \text{ for every }x\in\mathcal I(z)\Bigr\} \]
is the library's `incomingPolar (sourceJump z) (sourceCurvature z)`. -/
theorem incoming_set_eq {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η δ : ℝ)
    (z : PointwiseFeasibility.BandPoint F K Fstar η) :
    PointwiseFeasibility.incomingPolar (PointwiseFeasibility.sourceJump (c₁ := c₁) (c₂ := c₂)
        (δ := δ) z) (PointwiseFeasibility.sourceCurvature z) =
      {v | ∀ x : PointwiseFeasibility.IncomingPoint F K Fstar c₁ c₂ η δ z,
        |dot (coordinateGradient F z.val - coordinateGradient F x.val.val) v| ≤
          Real.sqrt (dot (coordinateGradient F z.val - coordinateGradient F x.val.val)
            (z.val - x.val.val))} := rfl

/-- Item `C/05_G/disp/012` (`companion/chapters/05_G.tex:129-131`), equation `G:eq:nu`:
\[ \nu(z)=\sup_{v\in\mathcal D(z)}|\nabla F(z)^Tv|\in[0,\infty], \]
an extended nonnegative real; the library's `sourceCapacity F K Fstar c₁ c₂ η δ z`. -/
theorem nu_eq {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η δ : ℝ)
    (z : PointwiseFeasibility.BandPoint F K Fstar η) :
    PointwiseFeasibility.sourceCapacity F K Fstar c₁ c₂ η δ z =
      sSup ((fun v => ENNReal.ofReal |dot (coordinateGradient F z.val) v|) ''
        PointwiseFeasibility.incomingPolar (PointwiseFeasibility.sourceJump (c₁ := c₁) (c₂ := c₂)
          (δ := δ) z) (PointwiseFeasibility.sourceCurvature z)) := by
  rw [sSup_image']
  rfl

/-- Item `C/05_G/prose/020` (`companion/chapters/05_G.tex:132`): "An empty predecessor set
gives $\mathcal D(z)=\R^n$." -/
theorem empty_predecessors {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η δ : ℝ)
    (z : PointwiseFeasibility.BandPoint F K Fstar η)
    (hempty : IsEmpty (PointwiseFeasibility.IncomingPoint F K Fstar c₁ c₂ η δ z)) :
    PointwiseFeasibility.incomingPolar (PointwiseFeasibility.sourceJump (c₁ := c₁) (c₂ := c₂)
      (δ := δ) z) (PointwiseFeasibility.sourceCurvature z) = univ :=
  PointwiseFeasibility.incomingPolar_empty _ _

/-- Item `C/05_G/prose/021` (`companion/chapters/05_G.tex:132`): "The set $\mathcal D(z)$
is the polar of the closed absolutely convex hull of the normalized incoming jumps $y/\sqrt t$."
With $y=\nabla F(z)-\nabla F(x)$, $t=t(x,z)$ for $x\in\mathcal I(z)$ (and $c_2<1$, so $t>0$),
$\mathcal D(z)=\{v:|w^Tv|\le1\text{ for all }w\in\overline{\operatorname{absconv}}\{y/\sqrt t\}\}$. -/
theorem polar_description {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η δ : ℝ)
    (hc₂ : c₂ < 1) (z : PointwiseFeasibility.BandPoint F K Fstar η) :
    PointwiseFeasibility.incomingPolar (PointwiseFeasibility.sourceJump (c₁ := c₁) (c₂ := c₂)
        (δ := δ) z) (PointwiseFeasibility.sourceCurvature z) =
      {v | ∀ w ∈ closedAbsConvexHull ℝ (Set.range
          (fun x : PointwiseFeasibility.IncomingPoint F K Fstar c₁ c₂ η δ z =>
            (Real.sqrt (PointwiseFeasibility.sourceCurvature z x))⁻¹ •
              PointwiseFeasibility.sourceJump z x)), |dot w v| ≤ 1} := by
  rw [PointwiseFeasibility.sourceIncomingPolar_eq_closedHull_polar hc₂ z]
  ext v
  simp only [LinearMap.polar, Set.mem_setOf_eq, PointwiseFeasibility.dotPairing_apply,
    Real.norm_eq_abs]

/-- Item `C/05_G/proposition/002` (`companion/chapters/05_G.tex:134-140`), Proposition 5.3.1 (Exact
characterization of (V) and (S), without transport), with display `disp/013`. Under the standing
assumptions of Section 5.1, for a fixed threshold $\delta>0$: a finite-valued PSD field with
(5.V) (uniform $m>0$) and (5.S) (finite $C$, pairs with $d\le\delta$) exists if and only if
\[ \inf_z\nu(z)>0, \]
the infimum over the differentiable points of the band. The statement concerns only (V) and
(S). -/
theorem pointwise_characterization {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η) (Kη : Set (Vec n))
    (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) (δ : ℝ) (hδ : 0 < δ) :
    (∃ (W : Vec n → Mat n) (m C : ℝ), 0 < m ∧
        (∀ x ∈ Kη, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
          dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x))) ↔
      0 < ⨅ z, PointwiseFeasibility.sourceCapacity F K Fstar c₁ c₂ η δ z := by
  rw [← PointwiseFeasibility.visibility_secant_iff_source_capacity F K Fstar c₁ c₂ η δ hc.2.2 hδ]
  subst hKη
  constructor
  · rintro ⟨W, m, C, hm, hpsd, hvis, hsec⟩
    exact ⟨{ W := W, m := m, C := C, δ := δ, m_pos := hm, delta_pos := hδ,
             positive_semidefinite := hpsd, visibility := hvis,
             secant := fun x z g h hx hz hp hd => hsec x hx z hz g h hp hd }, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨B.W, B.m, B.C, B.m_pos, fun x hx hd => B.positive_semidefinite x hx hd,
      fun x hx g hg => B.visibility x hx g hg,
      fun x hx z hz g h hp hd => B.secant x z g h hx hz hp hd⟩

/-- Item `C/05_G/disp/014` (`companion/chapters/05_G.tex:143-145`), in the proof of the
Proposition (Exact characterization of (V) and (S)): if $C>0$ and $W$ satisfies (5.V)--(5.S),
put $h=\nabla F(z)$ and
\[ v=\frac{W(z)h}{\sqrt C\sqrt{h^TW(z)h}}. \]
Then (next sentence) $|y^Tv|\le\sqrt t$ for every incoming pair $x\in\mathcal I(z)$ and
$|h^Tv|\ge\sqrt{m/C}$. -/
theorem proof_direction {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (_hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η) (δ : ℝ) (_hδ : 0 < δ)
    (B : VisibilitySecantCertificate F K Fstar c₁ c₂ η) (hBδ : B.δ = δ) (hC : 0 < B.C)
    (z : PointwiseFeasibility.BandPoint F K Fstar η) (h : Vec n)
    (hh : h = coordinateGradient F z.val) (v : Vec n)
    (hv : v = (Real.sqrt B.C * Real.sqrt (dot h (B.W z.val *ᵥ h)))⁻¹ • (B.W z.val *ᵥ h)) :
    (∀ x : PointwiseFeasibility.IncomingPoint F K Fstar c₁ c₂ η δ z,
      |dot (h - coordinateGradient F x.val.val) v| ≤
        Real.sqrt (dot (h - coordinateGradient F x.val.val) (z.val - x.val.val))) ∧
      Real.sqrt (B.m / B.C) ≤ |dot h v| := by
  have hgz := hasFDerivAt_coordinateGradient z.property.2
  rw [← hh] at hgz
  have hW := B.positive_semidefinite z.val z.property.1 z.property.2
  have hq : B.m ≤ dot h (B.W z.val *ᵥ h) := B.visibility z.val z.property.1 h hgz
  have hqpos : 0 < dot h (B.W z.val *ᵥ h) := lt_of_lt_of_le B.m_pos hq
  have hsC := Real.sqrt_pos.mpr hC
  have hsq := Real.sqrt_pos.mpr hqpos
  have hden : 0 < Real.sqrt B.C * Real.sqrt (dot h (B.W z.val *ᵥ h)) := mul_pos hsC hsq
  have hWs : (B.W z.val)ᵀ = B.W z.val := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hW.isHermitian
  have hdotW : ∀ u : Vec n, dot u (B.W z.val *ᵥ h) = dot (B.W z.val *ᵥ u) h := by
    intro u
    rw [CertificateGeometry.dot_mulVec, hWs]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨xv, hxv⟩, hp, hdx⟩
    dsimp only
    rw [← hh] at hp
    have hsec := B.secant xv z.val (coordinateGradient F xv) h hxv.1 z.property.1 hp
      (by rw [hBδ]; exact hdx)
    set y := h - coordinateGradient F xv with hy
    set t := dot y (z.val - xv) with ht
    have hsec' : metricEnergy (B.W z.val) y ≤ B.C * t := hsec
    have hcs := QuadraticGauge.metric_cauchy_schwarz hW y h
    have hyy : 0 ≤ metricEnergy (B.W z.val) y := by
      simpa only [metricEnergy, dot, star_trivial] using hW.2 y
    rw [hv, dot_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hden)]
    rw [inv_mul_le_iff₀ hden]
    have habs : |dot y (B.W z.val *ᵥ h)| ≤
        Real.sqrt (metricEnergy (B.W z.val) y) * Real.sqrt (dot h (B.W z.val *ᵥ h)) := by
      rw [← Real.sqrt_mul hyy, ← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      rw [hdotW]
      exact hcs
    have hyC : Real.sqrt (metricEnergy (B.W z.val) y) ≤ Real.sqrt B.C * Real.sqrt t := by
      rw [← Real.sqrt_mul hC.le]
      exact Real.sqrt_le_sqrt hsec'
    calc |dot y (B.W z.val *ᵥ h)| ≤
        Real.sqrt (metricEnergy (B.W z.val) y) * Real.sqrt (dot h (B.W z.val *ᵥ h)) := habs
      _ ≤ Real.sqrt B.C * Real.sqrt t * Real.sqrt (dot h (B.W z.val *ᵥ h)) :=
          mul_le_mul_of_nonneg_right hyC hsq.le
      _ = Real.sqrt B.C * Real.sqrt (dot h (B.W z.val *ᵥ h)) * Real.sqrt t := by ring
  · rw [hv, dot_smul_right]
    have hq2 : Real.sqrt (dot h (B.W z.val *ᵥ h)) * Real.sqrt (dot h (B.W z.val *ᵥ h)) =
        dot h (B.W z.val *ᵥ h) := Real.mul_self_sqrt hqpos.le
    have heq : (Real.sqrt B.C * Real.sqrt (dot h (B.W z.val *ᵥ h)))⁻¹ *
        dot h (B.W z.val *ᵥ h) = Real.sqrt (dot h (B.W z.val *ᵥ h)) / Real.sqrt B.C := by
      calc (Real.sqrt B.C * Real.sqrt (dot h (B.W z.val *ᵥ h)))⁻¹ * dot h (B.W z.val *ᵥ h)
          = (Real.sqrt B.C * Real.sqrt (dot h (B.W z.val *ᵥ h)))⁻¹ *
              (Real.sqrt (dot h (B.W z.val *ᵥ h)) * Real.sqrt (dot h (B.W z.val *ᵥ h))) := by
            rw [hq2]
        _ = Real.sqrt (dot h (B.W z.val *ᵥ h)) / Real.sqrt B.C := by
            field_simp
            linear_combination (-Real.sqrt B.C) * hq2
    rw [heq, abs_of_nonneg (div_nonneg hsq.le hsC.le), Real.sqrt_div' _ hC.le]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hq) hsC.le

/-- Item `C/05_G/prose/022` (`companion/chapters/05_G.tex:151`): "Thus higher rank adds no
pointwise power to (V) and (S)" (since 15 October 2026, wording point W17; before "(V)--(S)").
Under the standing assumptions of Section 5.1 and a threshold
$\delta>0$, if some finite-valued PSD field satisfies (5.V) and (5.S), then a rank-one field
$W(x)=v(x)v(x)^T$ satisfies (5.V) (with some $m'>0$) and (5.S) with $C=1$. -/
theorem rank_one_suffices {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η) (Kη : Set (Vec n))
    (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) (δ : ℝ) (hδ : 0 < δ)
    (hfield : ∃ (W : Vec n → Mat n) (m C : ℝ), 0 < m ∧
        (∀ x ∈ Kη, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
          dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
          EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
            dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x))) :
    ∃ (v : Vec n → Vec n) (m' : ℝ), 0 < m' ∧
      (∀ x ∈ Kη, ∀ g : Vec n, HasFDerivAt F (gradientFunctional g) x →
        dot g (outer (v x) (v x) *ᵥ g) ≥ m') ∧
      (∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
        EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
          dot (h - g) (outer (v z) (v z) *ᵥ (h - g)) ≤ 1 * dot (h - g) (z - x)) := by
  classical
  subst hKη
  obtain ⟨W, m, C, hm, hpsd, hvis, hsec⟩ := hfield
  let B : VisibilitySecantCertificate F K Fstar c₁ c₂ η :=
    { W := W, m := m, C := C, δ := δ, m_pos := hm, delta_pos := hδ,
      positive_semidefinite := hpsd, visibility := hvis,
      secant := fun x z g h hx hz hp hd => hsec x hx z hz g h hp hd }
  have hU := (PointwiseFeasibility.source_uniformPSD_iff F K Fstar c₁ c₂ η δ hδ).mpr ⟨B, rfl⟩
  have ht : ∀ (z : PointwiseFeasibility.BandPoint F K Fstar η)
      (x : PointwiseFeasibility.IncomingPoint F K Fstar c₁ c₂ η δ z),
      0 ≤ PointwiseFeasibility.sourceCurvature z x :=
    fun z x => (eligible_t_pos hc.2.2 x.property.1).le
  obtain ⟨r, hr, hdir⟩ := PointwiseFeasibility.uniformDirections_of_uniformPSD ht hU
  choose vz hvz hvis' using hdir
  let v : Vec n → Vec n := fun x =>
    if hx : x ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F x then vz ⟨x, hx⟩ else 0
  have hv : ∀ x (hx : x ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F x),
      v x = vz ⟨x, hx⟩ := fun x hx => dif_pos hx
  refine ⟨v, r ^ 2, sq_pos_of_pos hr, fun x hx g hg => ?_, fun x hx z hz g h hp hd => ?_⟩
  · have hx' : x ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F x := ⟨hx, hg.differentiableAt⟩
    have hgEq := PointwiseFeasibility.coordinateGradient_eq hg
    have h1 := hvis' ⟨x, hx'⟩
    simp only [hgEq] at h1
    rw [outer_mulVec, dot_smul_right, hv x hx']
    have hc : dot (vz ⟨x, hx'⟩) g = dot g (vz ⟨x, hx'⟩) := dotProduct_comm _ _
    rw [hc]
    nlinarith [sq_abs (dot g (vz ⟨x, hx'⟩)), abs_nonneg (dot g (vz ⟨x, hx'⟩))]
  · have hgEq := PointwiseFeasibility.coordinateGradient_eq hp.gradient_x
    have hhEq := PointwiseFeasibility.coordinateGradient_eq hp.gradient_z
    let zp : PointwiseFeasibility.BandPoint F K Fstar η := ⟨z, hz, hp.gradient_z.differentiableAt⟩
    let xp : PointwiseFeasibility.IncomingPoint F K Fstar c₁ c₂ η δ zp :=
      ⟨⟨x, hx, hp.gradient_x.differentiableAt⟩, by simpa only [zp, hgEq, hhEq] using hp,
        by simpa only [hgEq] using hd⟩
    have h1 := hvz zp xp
    have h1' : |dot (h - g) (vz zp)| ≤ Real.sqrt (dot (h - g) (z - x)) := by
      simpa only [PointwiseFeasibility.sourceJump, PointwiseFeasibility.sourceCurvature, zp, xp,
        hgEq, hhEq, pairCurvature, pairStep] using h1
    have htpos : 0 ≤ dot (h - g) (z - x) := (eligible_t_pos hc.2.2 hp).le
    have hvz' : v z = vz zp := hv z ⟨hz, hp.gradient_z.differentiableAt⟩
    rw [outer_mulVec, dot_smul_right, hvz', one_mul]
    rw [show dot (vz zp) (h - g) = dot (h - g) (vz zp) from dotProduct_comm _ _]
    nlinarith [sq_abs (dot (h - g) (vz zp)), abs_nonneg (dot (h - g) (vz zp)),
      Real.sq_sqrt htpos, Real.sqrt_nonneg (dot (h - g) (z - x))]

/-! ### Section 5.3.1: a nonexistence test independent of the certificate (lines 156-188) -/

/-- Item `C/05_G/proposition/G:prop:star` (`companion/chapters/05_G.tex:159-167`), Proposition
5.3.2 = `G:prop:star` (Incoming-jump obstruction), with display `disp/015`. Under the standing
assumptions of Section 5.1: let $z_\varepsilon$ and finitely many predecessors
$x_{j,\varepsilon}$ ($j<r$) give eligible pairs in the fixed band $K_\eta$, all endpoints
differentiable, with $d_{j,\varepsilon}\to0$. Write
$y_{j,\varepsilon}=\nabla F(z_\varepsilon)-\nabla F(x_{j,\varepsilon})$ and
$t_{j,\varepsilon}=y_{j,\varepsilon}^T(z_\varepsilon-x_{j,\varepsilon})$. If
\[ \nabla F(z_\varepsilon)=\sum_j\lambda_{j,\varepsilon}y_{j,\varepsilon},\qquad
   \sum_j|\lambda_{j,\varepsilon}|\sqrt{t_{j,\varepsilon}}\longrightarrow0, \]
then no field satisfies (V) and (S) (`visibilitySecant_iff`), and hence no transported
certificate exists on that band. The parameter $\varepsilon$ ranges over any index type with a
nontrivial limit filter `l` ("$\varepsilon\to0$"); `incoming_jump_obstruction_pos` is the case
$\varepsilon\downarrow0$. -/
theorem incoming_jump_obstruction {ι : Type*} {l : Filter ι} [NeBot l] {n r : ℕ}
    {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F) (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar)
    (b : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η)
    (z h : ι → Vec n) (x g : ι → Fin r → Vec n)
    (hz : ∀ ε, z ε ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hx : ∀ ε j, x ε j ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hdiff : ∀ ε, HasFDerivAt F (gradientFunctional (h ε)) (z ε))
    (hp : ∀ ε j, EligiblePair F c₁ c₂ (x ε j) (z ε) (g ε j) (h ε))
    (hd : ∀ j, Tendsto (fun ε => -dot (g ε j) (z ε - x ε j)) l (𝓝 0))
    (y : ι → Fin r → Vec n) (hy : ∀ ε j, y ε j = h ε - g ε j)
    (t : ι → Fin r → ℝ) (ht : ∀ ε j, t ε j = dot (y ε j) (z ε - x ε j))
    (lam : ι → Fin r → ℝ) (hrep : ∀ ε, h ε = ∑ j, lam ε j • y ε j)
    (hcost : Tendsto (fun ε => ∑ j, |lam ε j| * Real.sqrt (t ε j)) l (𝓝 0)) :
    ¬ Nonempty (VisibilitySecantCertificate F K Fstar c₁ c₂ η) ∧
      ¬ Nonempty (BandCertificate F K Fstar c₁ c₂ η) := by
  have hrep' : ∀ᶠ ε in l, h ε = ∑ j, lam ε j • (h ε - g ε j) :=
    Eventually.of_forall fun ε => by
      have := hrep ε
      simp only [hy] at this
      exact this
  have hcost' : Tendsto (fun ε => ∑ j, |lam ε j| *
      Real.sqrt (pairCurvature (x ε j) (z ε) (g ε j) (h ε))) l (𝓝 0) := by
    refine hcost.congr fun ε => ?_
    simp only [ht, hy, pairCurvature, pairStep]
  exact ⟨incoming_jump_no_visibility_secant hc.2.2 z h x g lam hz hx hdiff hp hd hrep' hcost',
    incoming_jump_no_band_certificate hc.2.2 z h x g lam hz hx hdiff hp hd hrep' hcost'⟩

/-- The case $\varepsilon\downarrow0$ of `incoming_jump_obstruction`: families indexed by
$\varepsilon>0$, limits as $\varepsilon\to0^+$. -/
theorem incoming_jump_obstruction_pos {n r : ℕ}
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar)
    (b : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η)
    (z h : ℝ → Vec n) (x g : ℝ → Fin r → Vec n)
    (hz : ∀ ε > 0, z ε ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hx : ∀ ε > 0, ∀ j, x ε j ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hdiff : ∀ ε > 0, HasFDerivAt F (gradientFunctional (h ε)) (z ε))
    (hp : ∀ ε > 0, ∀ j, EligiblePair F c₁ c₂ (x ε j) (z ε) (g ε j) (h ε))
    (hd : ∀ j, Tendsto (fun ε => -dot (g ε j) (z ε - x ε j)) (𝓝[>] 0) (𝓝 0))
    (y : ℝ → Fin r → Vec n) (hy : ∀ ε > 0, ∀ j, y ε j = h ε - g ε j)
    (t : ℝ → Fin r → ℝ) (ht : ∀ ε > 0, ∀ j, t ε j = dot (y ε j) (z ε - x ε j))
    (lam : ℝ → Fin r → ℝ) (hrep : ∀ ε > 0, h ε = ∑ j, lam ε j • y ε j)
    (hcost : Tendsto (fun ε => ∑ j, |lam ε j| * Real.sqrt (t ε j)) (𝓝[>] 0) (𝓝 0)) :
    ¬ Nonempty (VisibilitySecantCertificate F K Fstar c₁ c₂ η) ∧
      ¬ Nonempty (BandCertificate F K Fstar c₁ c₂ η) := by
  let l : Filter (Ioi (0 : ℝ)) := Filter.comap Subtype.val (𝓝[>] 0)
  haveI : NeBot l := by
    apply Filter.NeBot.comap_of_range_mem inferInstance
    rw [Subtype.range_coe]
    exact self_mem_nhdsWithin
  have hcomap : Tendsto (Subtype.val : Ioi (0 : ℝ) → ℝ) l (𝓝[>] 0) := tendsto_comap
  exact incoming_jump_obstruction (l := l) hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη
    (fun e => z e.val) (fun e => h e.val) (fun e => x e.val) (fun e => g e.val)
    (fun e => hz e.val e.property) (fun e => hx e.val e.property)
    (fun e => hdiff e.val e.property) (fun e => hp e.val e.property)
    (fun j => (hd j).comp hcomap) (fun e => y e.val) (fun e => hy e.val e.property)
    (fun e => t e.val) (fun e => ht e.val e.property) (fun e => lam e.val)
    (fun e => hrep e.val e.property) (hcost.comp hcomap)

/-- $\sqrt{\max(C,0)}=\sqrt C$ (the real square root vanishes on $(-\infty,0]$). -/
theorem sqrt_max_zero (C : ℝ) : Real.sqrt (max C 0) = Real.sqrt C := by
  rcases le_total C 0 with hC | hC
  · rw [max_eq_right hC, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos hC]
  · rw [max_eq_left hC]

/-- Item `C/05_G/disp/016` (`companion/chapters/05_G.tex:170-173`), in the proof of Proposition
`G:prop:star`: for any PSD field satisfying (S) (constant $C$, threshold $\delta>0$), the
triangle inequality for the seminorm induced by $W(z_\varepsilon)$ gives, for $\varepsilon$ near
the limit (once every $d_{j,\varepsilon}\le\delta$),
\[ \sqrt{\nabla F(z_\varepsilon)^TW(z_\varepsilon)\nabla F(z_\varepsilon)}
   \le\sqrt C\sum_j|\lambda_{j,\varepsilon}|\sqrt{t_{j,\varepsilon}}\to0. \] -/
theorem seminorm_display {ι : Type*} {l : Filter ι} {n r : ℕ}
    {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F) (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar)
    (b : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η) (Kη : Set (Vec n))
    (_hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η})
    (z h : ι → Vec n) (x g : ι → Fin r → Vec n)
    (hz : ∀ ε, z ε ∈ Kη) (hx : ∀ ε j, x ε j ∈ Kη)
    (hdiff : ∀ ε, HasFDerivAt F (gradientFunctional (h ε)) (z ε))
    (hp : ∀ ε j, EligiblePair F c₁ c₂ (x ε j) (z ε) (g ε j) (h ε))
    (hd : ∀ j, Tendsto (fun ε => -dot (g ε j) (z ε - x ε j)) l (𝓝 0))
    (y : ι → Fin r → Vec n) (hy : ∀ ε j, y ε j = h ε - g ε j)
    (t : ι → Fin r → ℝ) (ht : ∀ ε j, t ε j = dot (y ε j) (z ε - x ε j))
    (lam : ι → Fin r → ℝ) (hrep : ∀ ε, h ε = ∑ j, lam ε j • y ε j)
    (hcost : Tendsto (fun ε => ∑ j, |lam ε j| * Real.sqrt (t ε j)) l (𝓝 0))
    (W : Vec n → Mat n) (C δ : ℝ) (hδ : 0 < δ)
    (hpsd : ∀ x ∈ Kη, DifferentiableAt ℝ F x → (W x).PosSemidef)
    (hsec : ∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec n,
      EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ →
        dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) :
    (∀ᶠ ε in l, Real.sqrt (dot (h ε) (W (z ε) *ᵥ h ε)) ≤
        Real.sqrt C * ∑ j, |lam ε j| * Real.sqrt (t ε j)) ∧
      Tendsto (fun ε => Real.sqrt C * ∑ j, |lam ε j| * Real.sqrt (t ε j)) l (𝓝 0) := by
  have hsmall : ∀ᶠ ε in l, ∀ j, -dot (g ε j) (z ε - x ε j) ≤ δ := by
    apply eventually_all.mpr
    intro j
    exact ((hd j).eventually (eventually_lt_nhds hδ)).mono fun _ h => h.le
  refine ⟨?_, by simpa using hcost.const_mul (Real.sqrt C)⟩
  filter_upwards [hsmall] with ε hε
  have hW := hpsd (z ε) (hz ε) (hdiff ε).differentiableAt
  have htnn : ∀ j, 0 ≤ t ε j := fun j => by
    rw [ht, hy]
    exact (eligible_t_pos hc.2.2 (hp ε j)).le
  have hS : ∀ j, metricEnergy (W (z ε)) (y ε j) ≤ C * t ε j := fun j => by
    rw [ht, hy]
    exact hsec (x ε j) (hx ε j) (z ε) (hz ε) (g ε j) (h ε) (hp ε j) (hε j)
  have hb := IncomingJump.weighted_jump_bound hW (lam ε) (y ε) (t ε) C htnn hS
  rw [sqrt_max_zero, ← hrep ε] at hb
  exact hb

/-- Item `C/05_G/prose/024` (`companion/chapters/05_G.tex:176`): "In particular, the
obstruction holds if $n$ incoming jumps converge to a basis of $\R^n$, their curvature products
tend to zero, and endpoint gradients remain bounded." In the setting of Proposition
`G:prop:star` with $r=n$: if $y_{j,\varepsilon}\to b_j$ for a basis $(b_j)$,
$t_{j,\varepsilon}\to0$ and $\|\nabla F(z_\varepsilon)\|\le B$, no field satisfies (V) and (S)
and no transported certificate exists on the band. -/
theorem basis_obstruction {ι : Type*} {l : Filter ι} [NeBot l] {n : ℕ}
    {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F) (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar)
    (b : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η)
    (z h : ι → Vec n) (x g : ι → Fin n → Vec n)
    (hz : ∀ ε, z ε ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hx : ∀ ε j, x ε j ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hdiff : ∀ ε, HasFDerivAt F (gradientFunctional (h ε)) (z ε))
    (hp : ∀ ε j, EligiblePair F c₁ c₂ (x ε j) (z ε) (g ε j) (h ε))
    (hd : ∀ j, Tendsto (fun ε => -dot (g ε j) (z ε - x ε j)) l (𝓝 0))
    (basis : Basis (Fin n) ℝ (Vec n))
    (hy : ∀ j, Tendsto (fun ε => h ε - g ε j) l (𝓝 (basis j)))
    (ht : ∀ j, Tendsto (fun ε => dot (h ε - g ε j) (z ε - x ε j)) l (𝓝 0))
    (B : ℝ) (hB : ∀ ε, ‖h ε‖ ≤ B) :
    ¬ Nonempty (VisibilitySecantCertificate F K Fstar c₁ c₂ η) ∧
      ¬ Nonempty (BandCertificate F K Fstar c₁ c₂ η) :=
  ⟨basis_limit_no_visibility_secant hc.2.2 z h x g hz hx hdiff hp hd basis hy ht B
      (Eventually.of_forall hB),
    basis_limit_no_band_certificate hc.2.2 z h x g hz hx hdiff hp hd basis hy ht B
      (Eventually.of_forall hB)⟩

/-- Item `C/05_G/prose/025` (`companion/chapters/05_G.tex:176`): "The coefficients
expressing the gradient in that basis then remain bounded." If the jumps
$y_{j,\varepsilon}\to b_j$ (a basis) and $\|\nabla F(z_\varepsilon)\|\le B$, there is $D$ such
that, for $\varepsilon$ near the limit, every representation
$\nabla F(z_\varepsilon)=\sum_j\lambda_jy_{j,\varepsilon}$ has $|\lambda_j|\le D$ (the jumps
then form a basis, so the representation exists and is unique). -/
theorem basis_coefficients_bounded {ι : Type*} {l : Filter ι} {n : ℕ}
    (h : ι → Vec n) (y : ι → Fin n → Vec n) (basis : Basis (Fin n) ℝ (Vec n))
    (hy : ∀ j, Tendsto (fun ε => y ε j) l (𝓝 (basis j))) (B : ℝ) (hB : ∀ ε, ‖h ε‖ ≤ B) :
    ∃ D : ℝ, ∀ᶠ ε in l, (∃ lam : Fin n → ℝ, h ε = ∑ j, lam j • y ε j) ∧
      ∀ lam : Fin n → ℝ, h ε = ∑ j, lam j • y ε j → ∀ j, |lam j| ≤ D := by
  let Y : ι → Mat n := fun ε i j => y ε j i
  let Y₀ : Mat n := fun i j => basis j i
  have hY : Tendsto Y l (𝓝 Y₀) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (hy j).apply_nhds i
  have hdet : Y₀.det ≠ 0 := by
    have hunit := (Pi.basisFun ℝ (Fin n)).isUnit_det basis
    simpa only [Basis.det_apply, Basis.toMatrix_apply, Pi.basisFun_repr] using hunit.ne_zero
  have hInv : Tendsto (fun ε => (Y ε)⁻¹) l (𝓝 Y₀⁻¹) := by
    apply (continuousAt_matrix_inv Y₀ ?_).tendsto.comp hY
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  have hunit : ∀ᶠ ε in l, IsUnit (Y ε).det := by
    have hdlim := (continuous_id.matrix_det.continuousAt.tendsto).comp hY
    exact (hdlim.eventually (isOpen_ne.mem_nhds hdet)).mono
      (fun _ ha => isUnit_iff_ne_zero.mpr ha)
  have hinvbound : ∀ᶠ ε in l, ∀ j i, |(Y ε)⁻¹ j i| ≤ |Y₀⁻¹ j i| + 1 := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro i
    have hi := ((hInv.apply_nhds j).apply_nhds i).abs
    exact (hi.eventually (eventually_lt_nhds (lt_add_one _))).mono (fun _ ha => ha.le)
  have hsumY : ∀ ε (lam : Fin n → ℝ), ∑ j, lam j • y ε j = (Y ε).mulVec lam := by
    intro ε lam
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Y]
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨∑ j, ∑ i, (|Y₀⁻¹ j i| + 1) * max B 0, ?_⟩
  filter_upwards [hunit, hinvbound] with ε hu hb
  refine ⟨⟨(Y ε)⁻¹.mulVec (h ε), ?_⟩, fun lam hlam j => ?_⟩
  · rw [hsumY, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · have hl : lam = (Y ε)⁻¹.mulVec (h ε) := by
      rw [hlam, hsumY, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have hj : |lam j| ≤ ∑ i, (|Y₀⁻¹ j i| + 1) * max B 0 := by
      rw [hl]
      calc |((Y ε)⁻¹.mulVec (h ε)) j| = |∑ i, (Y ε)⁻¹ j i * h ε i| := rfl
        _ ≤ ∑ i, |(Y ε)⁻¹ j i * h ε i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (|Y₀⁻¹ j i| + 1) * max B 0 := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul]
          apply mul_le_mul (hb j i) _ (abs_nonneg _) (by positivity)
          exact ((show |h ε i| ≤ ‖h ε‖ by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (h ε) i).trans
            (hB ε)).trans (le_max_left B 0)
    refine hj.trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ i, (|Y₀⁻¹ j i| + 1) * max B 0)
      (fun j _ => Finset.sum_nonneg fun i _ => by positivity) (Finset.mem_univ j)

/-- Item `C/05_G/prose/027` (`companion/chapters/05_G.tex:178`): "Moreover, every eligible
pair is individually realizable as a first BFGS step." With "Hence $\alpha=1$ realizes it"
(line 182): for every eligible pair (and $c_2<1$) there is $H_0\succ0$ (the matrix of display
`disp/017`) such that the BFGS step from $x$ with $H_0$ and $\alpha=1$ lands at $z$, satisfies
the Armijo and weak Wolfe conditions, and has positive curvature $y^Ts>0$ (the update is
defined). -/
theorem eligible_pair_first_step {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ} (hc₂ : c₂ < 1)
    {x z g h : Vec n} (hp : EligiblePair F c₁ c₂ x z g h) :
    ∃ H₀ : Mat n, H₀.PosDef ∧ x + bfgsStep H₀ g 1 = z ∧
      F (x + bfgsStep H₀ g 1) ≤ F x + c₁ * dot g (bfgsStep H₀ g 1) ∧
      dot h (bfgsStep H₀ g 1) ≥ c₂ * dot g (bfgsStep H₀ g 1) ∧
      0 < dot (h - g) (bfgsStep H₀ g 1) := by
  have hd : 0 < -dot g (pairStep x z) := hp.decrease_pos
  refine ⟨realizingMetric g (pairStep x z), realizingMetric_posDef g _ hd, ?_, ?_, ?_, ?_⟩
  · rw [realizingMetric_step g _ hd, pairStep]
    abel
  · rw [realizingMetric_step g _ hd]
    have hz : x + pairStep x z = z := by rw [pairStep]; abel
    rw [hz]
    have := hp.armijo
    simp only [pairDecrease] at this
    linarith
  · rw [realizingMetric_step g _ hd]
    have hcurv := hp.curvature
    simp only [pairDecrease, pairCurvature] at hcurv
    have he : dot (h - g) (pairStep x z) = dot h (pairStep x z) - dot g (pairStep x z) := by
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [he] at hcurv
    linarith
  · rw [realizingMetric_step g _ hd]
    exact eligible_t_pos hc₂ hp

/-- Item `C/05_G/disp/017` (`companion/chapters/05_G.tex:179-181`): if $d=-g^Ts>0$, then
\[ H=\frac{ss^T}{d}+I-\frac{gg^T}{g^Tg}\succ0,\qquad Hg=-s. \] -/
theorem realizing_metric {n : ℕ} (g s : Vec n) (d : ℝ) (hd_def : d = -dot g s) (hd : 0 < d)
    (H : Mat n) (hH : H = d⁻¹ • outer s s + 1 - (dot g g)⁻¹ • outer g g) :
    H.PosDef ∧ H *ᵥ g = -s := by
  have hHeq : H = realizingMetric g s := by
    rw [hH, realizingMetric, CertificateGeometry.dot_self, ← hd_def]
    abel
  rw [hd_def] at hd
  rw [hHeq]
  exact ⟨realizingMetric_posDef g s hd, realizingMetric_mul_gradient g s hd⟩

/-- Item `C/05_G/prose/029` (`companion/chapters/05_G.tex:182`): "Positive definiteness
follows because a vector in both nullspaces would be parallel to $g$ and orthogonal to $s$, and
therefore zero." If $d=-g^Ts>0$ and $v$ lies in the null spaces of $ss^T/d$ and of
$I-gg^T/(g^Tg)$, then $v$ is parallel to $g$, orthogonal to $s$, and $v=0$. -/
theorem nullspaces_meet_trivially {n : ℕ} (g s : Vec n) (d : ℝ) (hd_def : d = -dot g s)
    (hd : 0 < d) (v : Vec n) (h1 : (d⁻¹ • outer s s) *ᵥ v = 0)
    (h2 : (1 - (dot g g)⁻¹ • outer g g) *ᵥ v = 0) :
    (∃ c : ℝ, v = c • g) ∧ dot s v = 0 ∧ v = 0 := by
  have hpar : v = ((dot g g)⁻¹ * dot g v) • g := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc, outer_mulVec, smul_smul,
      sub_eq_zero] at h2
    exact h2
  have hs : s ≠ 0 := by
    intro h0
    rw [h0] at hd_def
    simp [dot] at hd_def
    linarith
  have horth : dot s v = 0 := by
    rw [Matrix.smul_mulVec_assoc, outer_mulVec, smul_smul] at h1
    have hne : d⁻¹ * dot s v = 0 := by
      by_contra hne
      exact hs ((smul_eq_zero.mp h1).resolve_left hne)
    rcases mul_eq_zero.mp hne with h | h
    · exact absurd h (inv_ne_zero hd.ne')
    · exact h
  refine ⟨⟨_, hpar⟩, horth, ?_⟩
  have hsg : dot s g = -d := by rw [hd_def, neg_neg]; exact dotProduct_comm s g
  have hc : (dot g g)⁻¹ * dot g v = 0 := by
    have := horth
    rw [hpar, dot_smul_right, hsg] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (by linarith)
  rw [hpar, hc, zero_smul]

/-- Item `C/05_G/prose/078` (`companion/chapters/05_G.tex:359`): "The proof uses the
standard triangle inequality for a PSD seminorm." For PSD $W$,
$\sqrt{(\sum_j\lambda_jy_j)^TW(\sum_j\lambda_jy_j)}\le\sum_j|\lambda_j|\sqrt{y_j^TWy_j}$. -/
theorem psd_seminorm_triangle {n r : ℕ} {W : Mat n} (hW : W.PosSemidef) (coeff : Fin r → ℝ)
    (y : Fin r → Vec n) :
    Real.sqrt (dot (∑ j, coeff j • y j) (W *ᵥ ∑ j, coeff j • y j)) ≤
      ∑ j, |coeff j| * Real.sqrt (dot (y j) (W *ᵥ y j)) :=
  IncomingJump.sqrt_metricEnergy_sum_le hW coeff y

/-! ### Section 5.4: connection with tangent and normal geometry (lines 191-231) -/

/-- Item `C/05_G/disp/018` (`companion/chapters/05_G.tex:195-197`): for (limiting active)
gradients $g_1,\dots,g_r$,
\[ N=\operatorname{span}\{g_i-g_j\},\qquad U=N^\perp, \]
in $\R^n$ with the Euclidean inner product (`EuclideanSpace ℝ (Fin n)`); the library's
`jumpSpace` and `tangentSpace`. -/
theorem jumpSpace_eq {n r : ℕ} (g : Fin r → EuclideanSpace ℝ (Fin n)) :
    AccessibleJumpGeometry.jumpSpace g = Submodule.span ℝ {v | ∃ i j, v = g i - g j} ∧
      AccessibleJumpGeometry.tangentSpace g = (AccessibleJumpGeometry.jumpSpace g)ᗮ := by
  refine ⟨?_, rfl⟩
  rw [AccessibleJumpGeometry.jumpSpace, vectorSpan_def]
  congr 1
  ext v
  simp only [Set.mem_vsub, Set.mem_range, Set.mem_setOf_eq, vsub_eq_sub]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩

/-- Item `C/05_G/prose/030` (`companion/chapters/05_G.tex:198`): "The projected gradients
$P_Ug_i$ agree." -/
theorem projections_agree {n r : ℕ} (g : Fin r → EuclideanSpace ℝ (Fin n)) (i j : Fin r) :
    (AccessibleJumpGeometry.tangentSpace g).orthogonalProjection (g i) =
      (AccessibleJumpGeometry.tangentSpace g).orthogonalProjection (g j) :=
  AccessibleJumpGeometry.common_tangential_projection g i j

/-- An accessible limiting jump at $p$ (line 200): actual eligible pairs $(x_k,z_k)$ in the band
$K_\eta$ with both endpoints tending to $p$, $d\to0$, $t\to0$, and gradient jumps
$\nabla F(z_k)-\nabla F(x_k)\to j$. -/
def AccessibleJump {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η : ℝ)
    (p j : Vec n) : Prop :=
  ∃ x z g h : ℕ → Vec n,
    (∀ k, x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η} ∧ z k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η} ∧
      EligiblePair F c₁ c₂ (x k) (z k) (g k) (h k)) ∧
    Tendsto x atTop (𝓝 p) ∧ Tendsto z atTop (𝓝 p) ∧
    Tendsto (fun k => -dot (g k) (z k - x k)) atTop (𝓝 0) ∧
    Tendsto (fun k => dot (h k - g k) (z k - x k)) atTop (𝓝 0) ∧
    Tendsto (fun k => h k - g k) atTop (𝓝 j)

/-- Item `C/05_G/prose/033` (`companion/chapters/05_G.tex:204`): "Let $N_{\rm acc}$ be the
span of all such accessible limiting jumps, and set $U_{\rm acc}=N_{\rm acc}^{\perp}$." The
span, in `EuclideanSpace ℝ (Fin n)`, of the Euclidean images of all accessible limiting jumps at
$p$ (`AccessibleJump`); $U_{\rm acc}$ is `(accessibleSpan …)ᗮ`. -/
def accessibleSpan {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η : ℝ) (p : Vec n) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (euclideanVector '' {j | AccessibleJump F K Fstar c₁ c₂ η p j})

/-- Along an accessible sequence, a finite continuous extension of the field to $p$ gives
$W(z_k)\to W(p)$. -/
theorem field_limit {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ}
    (W : Vec n → Mat n) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto W (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p)
      (𝓝 Wp))
    (x z g h : ℕ → Vec n)
    (hp : ∀ k, x k ∈ positiveBand F K Fstar η ∧ z k ∈ positiveBand F K Fstar η ∧
      EligiblePair F c₁ c₂ (x k) (z k) (g k) (h k))
    (hz : Tendsto z atTop (𝓝 p)) : Tendsto (fun k => W (z k)) atTop (𝓝 Wp) :=
  hext.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hz, Eventually.of_forall fun k => ⟨(hp k).2.1, (hp k).2.2.gradient_z.differentiableAt⟩⟩)

/-- Item `C/05_G/disp/019` (`companion/chapters/05_G.tex:201-203`), with lines 200 and 204:
"For a certificate with a finite continuous extension to $p$, consider actual eligible incoming
pairs on the fixed positive band, with both endpoints tending to $p$, $d\to0$, $t\to0$, and
limiting gradient jump $j$. The secant inequality and continuity give
\[ j^TW(p)j=0,\qquad W(p)j=0, \]
where the second conclusion uses positive semidefiniteness." The extension is a matrix $W(p)$
with $W(z)\to W(p)$ as $z\to p$ through the differentiable band points. -/
theorem accessible_jump_annihilated {n : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K) (c₁ c₂ : ℝ)
    (_hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (_hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp))
    (j : Vec n) (hj : AccessibleJump F K Fstar c₁ c₂ η p j) :
    dot j (Wp *ᵥ j) = 0 ∧ Wp *ᵥ j = 0 := by
  obtain ⟨x, z, g, h, hp, _hx, hz, hd, ht, hy⟩ := hj
  have hW := field_limit Cert.W p Wp hext x z g h hp hz
  have h0 : Wp *ᵥ j = 0 :=
    AccessibleJumpGeometry.accessible_jump_annihilated Cert.toVisibilitySecant x z g h Wp j
      (Eventually.of_forall hp) hd ht hy hW
  refine ⟨?_, h0⟩
  rw [h0]
  simp [dot]

/-- Item `C/05_G/disp/020` (`companion/chapters/05_G.tex:205-207`): with $N_{\rm acc}$ the span
of all accessible limiting jumps and $U_{\rm acc}=N_{\rm acc}^\perp$,
\[ \operatorname{range}W(p)\subseteq U_{\rm acc}. \] -/
theorem range_in_accessible_tangent {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp)) :
    ∀ v ∈ LinearMap.range Wp.mulVecLin,
      euclideanVector v ∈ (accessibleSpan F K Fstar c₁ c₂ η p)ᗮ := by
  intro v hv
  by_cases hne : ∃ j, AccessibleJump F K Fstar c₁ c₂ η p j
  · obtain ⟨j₀, x, z, g, h, hp, _hx, hz, _hd, _ht, _hy⟩ := hne
    have hW := field_limit Cert.W p Wp hext x z g h hp hz
    have hpsd : Wp.PosSemidef := AccessibleJumpGeometry.posSemidef_limit hW
      (Eventually.of_forall fun k =>
        Cert.positive_semidefinite (z k) (hp k).2.1 (hp k).2.2.gradient_z.differentiableAt)
    have hsymm : Wp.IsSymm := by
      simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
        hpsd.isHermitian.eq
    have hann : ∀ i : {j // AccessibleJump F K Fstar c₁ c₂ η p j}, Wp.mulVec i.val = 0 :=
      fun i => (accessible_jump_annihilated hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp
        hext i.val i.property).2
    have h := AccessibleJumpGeometry.range_orthogonal_to_accessible_jumps Wp hsymm
      (fun i : {j // AccessibleJump F K Fstar c₁ c₂ η p j} => i.val) hann hv
    have hset : Set.range (fun i : {j // AccessibleJump F K Fstar c₁ c₂ η p j} =>
        euclideanVector i.val) = euclideanVector '' {j | AccessibleJump F K Fstar c₁ c₂ η p j} := by
      ext w
      simp
    rw [hset] at h
    exact h
  · have hempty : {j | AccessibleJump F K Fstar c₁ c₂ η p j} = ∅ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hj => hne ⟨j, hj⟩
    simp [accessibleSpan, hempty]

/-- `W(p)` annihilates the whole accessible span (`Matrix.toEuclideanLin` is $W(p)$ acting on
`EuclideanSpace ℝ (Fin n)`). -/
theorem accessibleSpan_le_ker {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp)) :
    accessibleSpan F K Fstar c₁ c₂ η p ≤ LinearMap.ker (Matrix.toEuclideanLin Wp) := by
  apply Submodule.span_le.mpr
  rintro a ⟨j, hj, rfl⟩
  have h0 := (accessible_jump_annihilated hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp
    hext j hj).2
  change Matrix.toEuclideanLin Wp (euclideanVector j) = 0
  ext k
  change (Wp.mulVec j) k = 0
  rw [h0]
  rfl

/-- Item `C/05_G/prose/034` (`companion/chapters/05_G.tex:208`): "For a limiting gradient
$g$ at which visibility persists, $g^TW(p)g>0$ implies $P_{U_{\rm acc}}g\ne0$." (Visibility
does persist at limits of gradients of band points: `visibility_persists`.) -/
theorem visible_accessible_projection {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp))
    (gl : Vec n) (hvis : 0 < dot gl (Wp *ᵥ gl)) :
    (accessibleSpan F K Fstar c₁ c₂ η p)ᗮ.orthogonalProjection (euclideanVector gl) ≠ 0 := by
  have hann : ∀ i : {j // AccessibleJump F K Fstar c₁ c₂ η p j}, Wp.mulVec i.val = 0 :=
    fun i => (accessible_jump_annihilated hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp
      hext i.val i.property).2
  have h := AccessibleJumpGeometry.visible_accessible_projection_ne_zero Wp
    (fun i : {j // AccessibleJump F K Fstar c₁ c₂ η p j} => i.val) hann gl hvis
  have hset : Set.range (fun i : {j // AccessibleJump F K Fstar c₁ c₂ η p j} =>
      euclideanVector i.val) = euclideanVector '' {j | AccessibleJump F K Fstar c₁ c₂ η p j} := by
    ext w
    simp
  rw [hset] at h
  exact h

/-- Visibility persists at a limiting gradient of band points: if $z_k\to p$ are differentiable
points of the band with $\nabla F(z_k)\to g$, then $g^TW(p)g\ge m>0$. -/
theorem visibility_persists {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ}
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp))
    (zs hs : ℕ → Vec n)
    (hzs : ∀ k, zs k ∈ positiveBand F K Fstar η ∧
      HasFDerivAt F (gradientFunctional (hs k)) (zs k))
    (hzp : Tendsto zs atTop (𝓝 p)) (gl : Vec n) (hgl : Tendsto hs atTop (𝓝 gl)) :
    Cert.m ≤ dot gl (Wp *ᵥ gl) := by
  have hW : Tendsto (fun k => Cert.W (zs k)) atTop (𝓝 Wp) :=
    hext.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hzp, Eventually.of_forall fun k => ⟨(hzs k).1, (hzs k).2.differentiableAt⟩⟩)
  exact AccessibleJumpGeometry.visibility_limit Cert.m hW hgl
    (Eventually.of_forall fun k => Cert.visibility (zs k) (hzs k).1 (hs k) (hzs k).2)

/-- Item `C/05_G/prose/036` (`companion/chapters/05_G.tex:210`): "A nonzero common
projection onto $U=N^\perp$ follows if the accessible jumps span $N$, or if $W(p)$ is otherwise
known to annihilate all active differences. Under that additional hypothesis, the common
projection is nonzero by visibility." For active gradients $g_1,\dots,g_r$ and a visible
$g_i$ ($g_i^TW(p)g_i>0$): if every difference $g_a-g_b$ lies in $N_{\rm acc}$, or if
$W(p)(g_a-g_b)=0$ for all $a,b$, then $P_Ug_i\ne0$. -/
theorem full_projection_ne_zero {n r : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp))
    (ga : Fin r → Vec n) (i : Fin r) (hvis : 0 < dot (ga i) (Wp *ᵥ ga i))
    (hyp : (∀ a c, euclideanVector (ga a - ga c) ∈ accessibleSpan F K Fstar c₁ c₂ η p) ∨
      (∀ a c, Wp *ᵥ (ga a - ga c) = 0)) :
    (AccessibleJumpGeometry.tangentSpace (fun a => euclideanVector (ga a))).orthogonalProjection
      (euclideanVector (ga i)) ≠ 0 := by
  have hann : ∀ a c, Wp *ᵥ (ga a - ga c) = 0 := by
    rcases hyp with hspan | hann
    · intro a c
      have hk := accessibleSpan_le_ker hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp hext
        (hspan a c)
      ext k
      exact congrArg (fun w : EuclideanSpace ℝ (Fin n) => w k) (LinearMap.mem_ker.mp hk)
    · exact hann
  exact AccessibleJumpGeometry.visible_tangent_projection_ne_zero Wp ga hann i hvis

/-- Item `C/05_G/disp/021` (`companion/chapters/05_G.tex:211-213`): independently of
accessibility,
\[ P_Ug_i=0\quad\Longleftrightarrow\quad0\in\operatorname{aff}\{g_1,\dots,g_r\}. \] -/
theorem projection_zero_iff_affine {n r : ℕ} (g : Fin r → EuclideanSpace ℝ (Fin n)) (i : Fin r) :
    (AccessibleJumpGeometry.tangentSpace g).orthogonalProjection (g i) = 0 ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (Set.range g) :=
  AccessibleJumpGeometry.tangent_projection_zero_iff_zero_mem_affineSpan g i

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/037` (`companion/chapters/05_G.tex:214`): "The affine-hull condition
is weaker than $0\in\conv\{g_1,\dots,g_r\}$ and need not imply stationarity for the convex
objective." $0\in\conv\Rightarrow0\in\aff$ for every finite family; for the limiting active
gradients $1,3$ of $f(x)=\frac12(x+2)^2+|x|$ at the kink $0$ (`limiting_gradients_at_kink`),
$0\in\aff\{1,3\}$ but $0\notin\conv\{1,3\}$, and $0$ is not a minimizer of $f$ (not
stationary). -/
theorem affine_weaker_than_convex :
    (∀ (n r : ℕ) (g : Fin r → EuclideanSpace ℝ (Fin n)),
      (0 : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (Set.range g) →
        (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (Set.range g)) ∧
    (0 : EuclideanSpace ℝ (Fin 1)) ∈
      affineSpan ℝ (Set.range fun i => euclideanVector (activeGradients i)) ∧
    (0 : EuclideanSpace ℝ (Fin 1)) ∉
      convexHull ℝ (Set.range fun i => euclideanVector (activeGradients i)) ∧
    ¬ (∀ x : ℝ, shiftedAbs 0 ≤ shiftedAbs x) := by
  refine ⟨fun n r g h => convexHull_subset_affineSpan _ h, ?_, ?_, ?_⟩
  · exact (AccessibleJumpGeometry.tangent_projection_zero_iff_zero_mem_affineSpan _ 0).mp
      (active_common_tangent_zero 0)
  · intro h0
    have hsub : convexHull ℝ (Set.range fun i => euclideanVector (activeGradients i)) ⊆
        {v : EuclideanSpace ℝ (Fin 1) | 1 ≤ v 0} := by
      apply convexHull_min
      · rintro _ ⟨i, rfl⟩
        fin_cases i <;> norm_num [activeGradients, euclideanVector, embed_apply]
      · intro u hu v hv a c ha hc hac
        simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hu hv ⊢
        nlinarith
    have := hsub h0
    norm_num at this
  · intro h
    have := h (-1)
    norm_num [shiftedAbs] at this

open ScalarCounterexamples in
/-- Item `C/05_G/prose/038` (`companion/chapters/05_G.tex:216`): "The distinction is
realized by the finite strongly convex objective" $f(x)=\frac12(x+2)^2+|x|$: it is real-valued
and $1$-strongly convex on $\R$ (and $F(x)=f(x_0)$ on $\R^1$ is convex). -/
theorem shifted_strongly_convex :
    StrongConvexOn univ 1 shiftedAbs ∧ ConvexOn ℝ univ shiftedObjective :=
  ⟨shiftedAbs_strongConvex, shiftedObjective_convex⟩

open ScalarCounterexamples in
/-- Item `C/05_G/disp/022` (`companion/chapters/05_G.tex:217-220`): the objective
\[ f(x)=\tfrac12(x+2)^2+|x|,\qquad (c_1,c_2)=(1/8,1/4), \]
is the library's `shiftedAbs` (on $\R$) and `shiftedObjective` (on $\R^1$, $F(x)=f(x_0)$); the
constants are the parameters used below. Its minimizer is $-1$, with $f(-1)=3/2$. -/
theorem shiftedAbs_eq :
    (∀ t, shiftedAbs t = (t + 2) ^ 2 / 2 + |t|) ∧ (∀ x, shiftedObjective x = shiftedAbs (x 0)) ∧
      (∀ t, shiftedAbs (-1) ≤ shiftedAbs t) ∧ shiftedAbs (-1) = 3 / 2 :=
  ⟨fun _ => rfl, fun _ => rfl, shiftedAbs_minimum, by norm_num [shiftedAbs]⟩

/-- A limiting gradient of $F$ at $p$: a limit of gradients $\nabla F(x_k)$ at differentiable
points $x_k\to p$ (the "limiting active gradients" of line 194). -/
def IsLimitingGradient {n : ℕ} (F : Vec n → ℝ) (p g : Vec n) : Prop :=
  ∃ x gs : ℕ → Vec n, (∀ k, HasFDerivAt F (gradientFunctional (gs k)) (x k)) ∧
    Tendsto x atTop (𝓝 p) ∧ Tendsto gs atTop (𝓝 g)

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/039` (`companion/chapters/05_G.tex:221`): "On every compact positive
band, $W\equiv1$ is a transported certificate." For $f(x)=\frac12(x+2)^2+|x|$ with
$(c_1,c_2)=(1/8,1/4)$, every compact $K$ and every $\eta>0$ there is a band certificate on
$K_\eta$ ($F_*=f(-1)$) with field $W\equiv1$. -/
theorem identity_certificate (K : Set (Vec 1)) (hK : IsCompact K) (η : ℝ) (hη : 0 < η) :
    ∃ Cert : BandCertificate shiftedObjective K (shiftedObjective (embed (-1))) (1 / 8) (1 / 4) η,
      Cert.W = fun _ => 1 :=
  ⟨identityCertificate hK hη (by norm_num), rfl⟩

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/040` (`companion/chapters/05_G.tex:221`): "Indeed, every eligible pair
with $d\le1/4$ stays on one smooth side of zero: a right-to-left crossing contradicts weak Wolfe,
and a left-to-right crossing contradicts Armijo and the small-decrease bound." -/
theorem small_pairs_same_side {x z g h : Vec 1}
    (hp : EligiblePair shiftedObjective (1 / 8) (1 / 4) x z g h) (hd : -dot g (z - x) ≤ 1 / 4) :
    ((0 < x 0 ∧ 0 < z 0) ∨ (x 0 < 0 ∧ z 0 < 0)) ∧ ¬ (0 < x 0 ∧ z 0 < 0) ∧
      ¬ (x 0 < 0 ∧ 0 < z 0) :=
  ⟨small_eligible_same_side (by norm_num) hp hd,
    fun hc => no_small_right_left_crossing hp hd hc.1 hc.2,
    fun hc => no_small_left_right_crossing (by norm_num) hp hd hc.1 hc.2⟩

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/041` (`companion/chapters/05_G.tex:221`): "Hence
$f'(z)-f'(x)=z-x$, proving (S) with $C=1$; transport is equality, and the positive-band gradient
bound proves visibility." For eligible pairs with $d\le1/4$: $y=s$, so
$y^TIy=1\cdot t$; $\Pi_sI\Pi_s-\Pi_sI\Pi_s=0$; and on a compact band $K_\eta$ the gradients are
bounded away from zero, $g^TIg\ge m>0$. -/
theorem identity_certificate_reasons :
    (∀ {x z g h : Vec 1}, EligiblePair shiftedObjective (1 / 8) (1 / 4) x z g h →
      -dot g (z - x) ≤ 1 / 4 →
        h - g = z - x ∧ dot (h - g) ((1 : Mat 1) *ᵥ (h - g)) = 1 * dot (h - g) (z - x) ∧
        stepProjector (z - x) * 1 * stepProjector (z - x) -
          stepProjector (z - x) * 1 * stepProjector (z - x) = 0) ∧
    ∀ (K : Set (Vec 1)), IsCompact K → ∀ η : ℝ, 0 < η → ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ positiveBand shiftedObjective K (shiftedObjective (embed (-1))) η, ∀ g : Vec 1,
        HasFDerivAt shiftedObjective (gradientFunctional g) x → dot g ((1 : Mat 1) *ᵥ g) ≥ m := by
  refine ⟨fun hp hd => ?_, fun K hK η hη => ?_⟩
  · have he := small_eligible_gradient_change (by norm_num) hp hd
    refine ⟨he, ?_, sub_self _⟩
    rw [he, one_mul, Matrix.one_mulVec]
  · obtain ⟨m, G, hm, _hG, hb⟩ := scalar_gradient_band_bounds shiftedObjective_convex
      (embed (-1)) hK hη
    refine ⟨m ^ 2, sq_pos_of_pos hm, fun x hx g hg => ?_⟩
    have h1 := (hb x hx g hg).1
    have : dot g ((1 : Mat 1) *ᵥ g) = (g 0) ^ 2 := by
      simp [dot, Matrix.one_mulVec, pow_two]
    rw [this]
    nlinarith [sq_abs (g 0), abs_nonneg (g 0)]

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/042` (`companion/chapters/05_G.tex:221`): "Weak Wolfe gives
$d\le4t/3$, so $t\to0$ eventually makes $d\le1/4$; as both endpoints tend to the same point,
every accessible limiting jump is therefore zero." For $f$ and $(c_1,c_2)=(1/8,1/4)$: every
eligible pair has $d\le\frac43t$, and on every band every accessible limiting jump
(`AccessibleJump`) at every point is $0$. -/
theorem accessible_jumps_vanish (K : Set (Vec 1)) (η : ℝ) :
    (∀ x z g h : Vec 1, EligiblePair shiftedObjective (1 / 8) (1 / 4) x z g h →
      -dot g (z - x) ≤ 4 / 3 * dot (h - g) (z - x)) ∧
    ∀ p j : Vec 1,
      AccessibleJump shiftedObjective K (shiftedObjective (embed (-1))) (1 / 8) (1 / 4) η p j →
        j = 0 := by
  refine ⟨fun x z g h hp => ?_, fun p j hj => ?_⟩
  · have := hp.curvature
    simp only [pairDecrease, pairCurvature, pairStep] at this
    linarith
  · obtain ⟨x, z, g, h, hp, hx, hz, _hd, ht, hy⟩ := hj
    exact accessible_jump_zero (by norm_num) x z g h p j
      (Eventually.of_forall fun k => (hp k).2.2) hx hz ht hy

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/043` (`companion/chapters/05_G.tex:221`): "Nevertheless the actual
limiting active gradients at zero are $1$ and $3$, so $N=\mathbb R$ and $U=\{0\}$." The
limiting gradients of $f$ at $0$ are exactly $1$ and $3$ (`activeGradients`), and for them
$N=\R$, $U=\{0\}$. -/
theorem limiting_gradients_at_kink :
    {g | IsLimitingGradient shiftedObjective 0 g} = {embed 1, embed 3} ∧
      Set.range activeGradients = {embed 1, embed 3} ∧
      AccessibleJumpGeometry.jumpSpace (fun i => euclideanVector (activeGradients i)) = ⊤ ∧
      AccessibleJumpGeometry.tangentSpace (fun i => euclideanVector (activeGradients i)) = ⊥ := by
  have hU := full_active_tangent_space_eq_bot
  refine ⟨?_, ?_, ?_, hU⟩
  · ext g
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, gs, hgrad, hx, hgs⟩
      have hval : ∀ k, gs k 0 - x k 0 ∈ ({1, 3} : Set ℝ) := by
        intro k
        rcases lt_or_gt_of_ne (actual_endpoint_ne_zero (hgrad k)) with hneg | hpos
        · rw [actual_gradient_neg (hgrad k) hneg]
          simp
        · rw [actual_gradient_pos (hgrad k) hpos]
          simp
      have hlim : Tendsto (fun k => gs k 0 - x k 0) atTop (𝓝 (g 0 - (0 : Vec 1) 0)) :=
        ((continuous_apply 0).tendsto g |>.comp hgs).sub ((continuous_apply 0).tendsto _ |>.comp hx)
      have hmem := (Set.toFinite ({1, 3} : Set ℝ)).isClosed.mem_of_tendsto hlim
        (Eventually.of_forall hval)
      simp only [Pi.zero_apply, sub_zero, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h1 | h3
      · left
        rw [← embed_eval g, h1]
      · right
        rw [← embed_eval g, h3]
    · rintro (rfl | rfl)
      · exact ⟨activeApproach 0, activeGradientApproach 0, active_approach_actual_gradient 0,
          active_approach_tendsto 0, active_gradient_approach_tendsto 0⟩
      · exact ⟨activeApproach 1, activeGradientApproach 1, active_approach_actual_gradient 1,
          active_approach_tendsto 1, active_gradient_approach_tendsto 1⟩
  · ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  · have h := congrArg (fun S => Sᗮ) hU
    simpa [AccessibleJumpGeometry.tangentSpace, Submodule.orthogonal_orthogonal] using h

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/044` (`companion/chapters/05_G.tex:221`): "The full-active
tangential conclusion would be false here." On the compact band $\{f\le3\}_{1/4}$, which
contains the kink $0$, the continuous certificate $W\equiv1$ ($(c_1,c_2)=(1/8,1/4)$) is visible
at both limiting active gradients $1,3$ at $0$ ($g^TW(0)g>0$), yet $P_Ug=0$ for $U=N^\perp$:
"$g^TW(p)g>0\Rightarrow P_Ug\ne0$" fails with $N$ the span of all active differences. -/
theorem full_active_conclusion_fails :
    ∃ Cert : BandCertificate shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 8) (1 / 4) (1 / 4),
      Cert.W = (fun _ => 1) ∧ Continuous Cert.W ∧
      (0 : Vec 1) ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 4) ∧
      (∀ i, IsLimitingGradient shiftedObjective 0 (activeGradients i)) ∧
      (∀ i, 0 < dot (activeGradients i) (Cert.W 0 *ᵥ activeGradients i)) ∧
      (∀ i, (AccessibleJumpGeometry.tangentSpace
          (fun j => euclideanVector (activeGradients j))).orthogonalProjection
        (euclideanVector (activeGradients i)) = 0) := by
  obtain ⟨B, hBW, hBc, hgrad, hlim, _hband, hvis, hproj⟩ :=
    objective_level_accessibility_counterexample
  exact ⟨B, hBW, hBc, kink_positive_band,
    fun i => ⟨activeApproach i, activeGradientApproach i, hgrad i, (hlim i).1, (hlim i).2⟩,
    hvis, hproj⟩

open ScalarCounterexamples OneDimensional in
/-- Item `C/05_G/prose/045` (`companion/chapters/05_G.tex:221`): "The later no-certificate
example uses the different constants $(1/4,1/2)$ and is consistent with this distinction." On
the compact sublevel $\{f\le3\}$ the band certificates exist for $(1/8,1/4)$ and fail for
$(1/4,1/2)$. -/
theorem constants_consistency :
    HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 8) (1 / 4) ∧
      ¬ HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) :=
  ⟨ShiftedAbsAccessibility.shifted_all_compact_band_certificates
      (shiftedObjective_sublevel_compact 3) (by norm_num),
    shifted_no_band_certificates⟩

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/048` (`companion/chapters/05_G.tex:223`): "Eligibility matters:
arbitrary active-gradient jumps need not be accessible under a fixed weak-Wolfe condition." For
$f$ and $(c_1,c_2)=(1/8,1/4)$ the active jump $3-1=2$ at the kink is not an accessible limiting
jump on any band. -/
theorem active_jump_not_accessible (K : Set (Vec 1)) (η : ℝ) :
    activeGradients 1 - activeGradients 0 ≠ 0 ∧
      ¬ AccessibleJump shiftedObjective K (shiftedObjective (embed (-1))) (1 / 8) (1 / 4) η 0
        (activeGradients 1 - activeGradients 0) := by
  have hne : activeGradients 1 - activeGradients 0 ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num [activeGradients, embed_apply] at this
  exact ⟨hne, fun hj => hne ((accessible_jumps_vanish K η).2 _ _ hj)⟩

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/prose/035` (`companion/chapters/05_G.tex:210`): "This conclusion concerns
the accessible span. It does not identify $N_{\rm acc}$ with the earlier space $N$ generated by
all active-gradient differences." For $f(x)=\frac12(x+2)^2+|x|$ and $(c_1,c_2)=(1/8,1/4)$, at
the kink $p=0$ (on every band) $N_{\rm acc}=\{0\}$, while the active gradients $1,3$ give
$N=\R$. -/
theorem accessible_span_differs (K : Set (Vec 1)) (η : ℝ) :
    accessibleSpan shiftedObjective K (shiftedObjective (embed (-1))) (1 / 8) (1 / 4) η 0 = ⊥ ∧
      AccessibleJumpGeometry.jumpSpace (fun i => euclideanVector (activeGradients i)) = ⊤ := by
  refine ⟨?_, limiting_gradients_at_kink.2.2.1⟩
  rw [eq_bot_iff, accessibleSpan, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [(accessible_jumps_vanish K η).2 0 j hj, SetLike.mem_coe, Submodule.mem_bot]
  exact WithLp.equiv_symm_zero 2

/-- $F(u,v)=u^2+|v|$ has gradient $(2u,\operatorname{sign}v)$ at every point with $v\ne0$. -/
theorem uv_hasGradient (F : Vec 2 → ℝ) (hF : ∀ x, F x = x 0 ^ 2 + |x 1|) {x : Vec 2}
    (hx : x 1 ≠ 0) :
    HasFDerivAt F (gradientFunctional ![2 * x 0, if 0 < x 1 then 1 else -1]) x := by
  have hFe : F = fun x : Vec 2 => x 0 ^ 2 + |x 1| := funext hF
  subst hFe
  have h0 : HasFDerivAt (fun x : Vec 2 => x 0) (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 0 x
  have h1 : HasFDerivAt (fun x : Vec 2 => x 1) (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)]
    have hsum := ((hasDerivAt_pow 2 (x 0)).comp_hasFDerivAt x h0).add
      ((hasDerivAt_abs_neg hneg).comp_hasFDerivAt x h1)
    convert hsum using 1
    ext v
    simp [gradientFunctional_apply, dot, Fin.sum_univ_two]
  · rw [if_pos hpos]
    have hsum := ((hasDerivAt_pow 2 (x 0)).comp_hasFDerivAt x h0).add
      ((hasDerivAt_abs_pos hpos).comp_hasFDerivAt x h1)
    convert hsum using 1
    ext v
    simp [gradientFunctional_apply, dot, Fin.sum_univ_two]

/-- Every gradient of $F(u,v)=u^2+|v|$ is taken at a point with $v\ne0$ and equals
$(2u,\operatorname{sign}v)$. -/
theorem uv_gradient_eq (F : Vec 2 → ℝ) (hF : ∀ x, F x = x 0 ^ 2 + |x 1|) {x g : Vec 2}
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    x 1 ≠ 0 ∧ g = ![2 * x 0, if 0 < x 1 then 1 else -1] := by
  have hx1 : x 1 ≠ 0 := by
    intro h0
    let e : Vec 2 := ![0, 1]
    have hline : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    have hcomp := hg.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have heq : (F ∘ fun t : ℝ => x + t • e) = fun t => x 0 ^ 2 + |t| := by
      funext t
      simp only [Function.comp_apply, hF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
      simp [h0]
    rw [heq] at hcomp
    have hd : DifferentiableAt ℝ (fun t : ℝ => (x 0 ^ 2 + |t|) - x 0 ^ 2) 0 :=
      hcomp.differentiableAt.sub (differentiableAt_const _)
    simp only [add_sub_cancel_left] at hd
    exact not_differentiableAt_abs_zero hd
  refine ⟨hx1, ?_⟩
  exact AffineProjection.gradientFunctional_injective (hg.unique (uv_hasGradient F hF hx1))

/-- The limiting gradients of $F(u,v)=u^2+|v|$ at $(u_0,0)$ are exactly $(2u_0,\pm1)$. -/
theorem uv_limiting_gradients (F : Vec 2 → ℝ) (hF : ∀ x, F x = x 0 ^ 2 + |x 1|) (u0 : ℝ) :
    {g | IsLimitingGradient F ![u0, 0] g} = {![2 * u0, 1], ![2 * u0, -1]} := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, gs, hgrad, hx, hgs⟩
    have hform := fun k => uv_gradient_eq F hF (hgrad k)
    have h0 : Tendsto (fun k => gs k 0) atTop (𝓝 (g 0)) :=
      (continuous_apply 0).tendsto g |>.comp hgs
    have h0' : Tendsto (fun k => gs k 0) atTop (𝓝 (2 * u0)) := by
      have hx0 : Tendsto (fun k => x k 0) atTop (𝓝 u0) := by
        simpa using ((continuous_apply 0).tendsto _).comp hx
      refine (hx0.const_mul 2).congr fun k => ?_
      rw [(hform k).2]
      simp
    have hg0 : g 0 = 2 * u0 := tendsto_nhds_unique h0 h0'
    have h1 : Tendsto (fun k => gs k 1) atTop (𝓝 (g 1)) :=
      (continuous_apply 1).tendsto g |>.comp hgs
    have hval : ∀ k, gs k 1 ∈ ({1, -1} : Set ℝ) := by
      intro k
      rw [(hform k).2]
      split_ifs <;> simp
    have hmem := (Set.toFinite ({1, -1} : Set ℝ)).isClosed.mem_of_tendsto h1
      (Eventually.of_forall hval)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · left
      ext i
      fin_cases i <;> simp [hg0, h]
    · right
      ext i
      fin_cases i <;> simp [hg0, h]
  · have hconv : ∀ σ : ℝ, Tendsto (fun k : ℕ => (![u0, σ / ((k : ℝ) + 1)] : Vec 2)) atTop
        (𝓝 ![u0, 0]) := by
      intro σ
      apply tendsto_pi_nhds.mpr
      intro i
      fin_cases i
      · simp
      · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul σ
        simp only [mul_zero, mul_one_div] at this
        simpa using this
    rintro (rfl | rfl)
    · refine ⟨fun k => ![u0, 1 / ((k : ℝ) + 1)], fun _ => ![2 * u0, 1], fun k => ?_,
        hconv 1, tendsto_const_nhds⟩
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hpos : 0 < (![u0, 1 / ((k : ℝ) + 1)] : Vec 2) 1 := by simp [hk]
      have h := uv_hasGradient F hF hpos.ne'
      rw [if_pos hpos] at h
      simpa using h
    · refine ⟨fun k => ![u0, -1 / ((k : ℝ) + 1)], fun _ => ![2 * u0, -1], fun k => ?_,
        hconv (-1), tendsto_const_nhds⟩
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hneg : (![u0, -1 / ((k : ℝ) + 1)] : Vec 2) 1 < 0 := by
        simp only [Matrix.cons_val_one, Matrix.head_cons]
        exact div_neg_of_neg_of_pos (by norm_num) hk
      have h := uv_hasGradient F hF hneg.ne
      rw [if_neg (not_lt.mpr hneg.le)] at h
      simpa using h

/-- Item `C/05_G/prose/049` (`companion/chapters/05_G.tex:225`): "For $u^2+|v|$ at $(u,0)$
with $u\ne0$, the jump space is vertical and a nonzero horizontal derivative remains." For
$F(u,v)=u^2+|v|$ and $u_0\ne0$: the limiting active gradients at $(u_0,0)$ are $(2u_0,\pm1)$,
their jump space is $N=\operatorname{span}\{e_2\}$, and $P_U$ of each of them is the nonzero
horizontal vector $(2u_0,0)$. -/
theorem uv_geometry (F : Vec 2 → ℝ) (hF : ∀ x, F x = x 0 ^ 2 + |x 1|) (u0 : ℝ) (hu0 : u0 ≠ 0) :
    {g | IsLimitingGradient F ![u0, 0] g} = {![2 * u0, 1], ![2 * u0, -1]} ∧
      AccessibleJumpGeometry.jumpSpace (fun i : Fin 2 =>
          euclideanVector (![![2 * u0, 1], ![2 * u0, -1]] i)) =
        Submodule.span ℝ {euclideanVector ![0, 1]} ∧
      ∀ i : Fin 2, ((AccessibleJumpGeometry.tangentSpace (fun i : Fin 2 =>
          euclideanVector (![![2 * u0, 1], ![2 * u0, -1]] i))).orthogonalProjection
            (euclideanVector (![![2 * u0, 1], ![2 * u0, -1]] i)) : EuclideanSpace ℝ (Fin 2)) =
          euclideanVector ![2 * u0, 0] ∧ euclideanVector ![2 * u0, 0] ≠ 0 := by
  let g : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
    fun i => euclideanVector (![![2 * u0, 1], ![2 * u0, -1]] i)
  let e : EuclideanSpace ℝ (Fin 2) := euclideanVector ![0, 1]
  have hrange : Set.range g = {g 0, g 1} := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hdiff : g 0 -ᵥ g 1 = (2 : ℝ) • e := by
    ext i
    fin_cases i <;> norm_num [g, e, euclideanVector]
  have hN : AccessibleJumpGeometry.jumpSpace g = Submodule.span ℝ {e} := by
    rw [AccessibleJumpGeometry.jumpSpace, hrange, vectorSpan_pair, hdiff]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (by norm_num)) e
  refine ⟨uv_limiting_gradients F hF u0, hN, fun i => ⟨?_, ?_⟩⟩
  · have hU : AccessibleJumpGeometry.tangentSpace g = (Submodule.span ℝ {e})ᗮ := by
      rw [AccessibleJumpGeometry.tangentSpace, hN]
    change ((AccessibleJumpGeometry.tangentSpace g).orthogonalProjection (g i) :
      EuclideanSpace ℝ (Fin 2)) = _
    rw [hU]
    apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
    · rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp [e, euclideanVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
        Fin.sum_univ_two]
    · intro w hw
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw
      have hsub : g i - euclideanVector ![2 * u0, 0] =
          (if i = 0 then (1 : ℝ) else -1) • e := by
        ext k
        fin_cases i <;> fin_cases k <;> simp [g, e, euclideanVector]
      rw [hsub, inner_smul_left, hw, mul_zero]
  · intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    simp [euclideanVector] at this
    exact hu0 this

/-- Literal form of item `C/05_G/prose/050` (line 225, "there may be no remaining comparison
direction"), in any dimension: under the hypotheses of display `disp/019` (a certificate with a
finite continuous extension $W(p)$), if the accessible jumps at $p$ span the whole space, then
$W(p)=0$, so no comparison direction remains ($g^TW(p)g=0$ for every $g$). When an accessible
jump exists these hypotheses can never all hold (`spanning_jumps_obstruction`), so this
implication is vacuous; the content of the sentence is the obstruction (`vertex_obstruction`). -/
theorem spanning_jumps_no_direction {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n) (Wp : Mat n)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp))
    (hspan : accessibleSpan F K Fstar c₁ c₂ η p = ⊤) :
    Wp = 0 ∧ ∀ gl : Vec n, dot gl (Wp *ᵥ gl) = 0 := by
  have hker := accessibleSpan_le_ker hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp hext
  rw [hspan] at hker
  have hzero : ∀ v : Vec n, Wp *ᵥ v = 0 := by
    intro v
    have hv := LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := euclideanVector v)))
    ext k
    exact congrArg (fun w : EuclideanSpace ℝ (Fin n) => w k) hv
  have hW : Wp = 0 := by
    ext i j
    have := congrFun (hzero (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  refine ⟨hW, fun gl => ?_⟩
  rw [hzero gl]
  simp [dot]

/-- The two-dimensional case of `spanning_jumps_no_direction` ("a generic two-dimensional vertex
with independent accessible jumps"): if two linearly independent jumps are accessible at $p$,
then $W(p)=0$. These hypotheses can never all hold (`vertex_obstruction`, independent review). -/
theorem vertex_no_direction {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec 2))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec 2) (Wp : Mat 2)
    (hext : Tendsto Cert.W
      (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p) (𝓝 Wp))
    (j₁ j₂ : Vec 2) (hj₁ : AccessibleJump F K Fstar c₁ c₂ η p j₁)
    (hj₂ : AccessibleJump F K Fstar c₁ c₂ η p j₂)
    (hind : LinearIndependent ℝ ![euclideanVector j₁, euclideanVector j₂]) :
    Wp = 0 ∧ ∀ gl : Vec 2, dot gl (Wp *ᵥ gl) = 0 := by
  refine spanning_jumps_no_direction hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp hext ?_
  have htop : Submodule.span ℝ (Set.range ![euclideanVector j₁, euclideanVector j₂]) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank (by simp)
  apply top_unique
  rw [← htop]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨j₁, hj₁, rfl⟩
  · exact ⟨j₂, hj₂, rfl⟩

/-- Visibility at differentiable band points $z_k\to p$ is incompatible with $W(z_k)\to0$: the
gradients of a finite convex function are bounded near $p$ (lemma of the independent review). -/
theorem no_vanishing_limit {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ} (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec n)
    (z h : ℕ → Vec n) (hz : ∀ k, z k ∈ positiveBand F K Fstar η)
    (hh : ∀ k, HasFDerivAt F (gradientFunctional (h k)) (z k))
    (hzp : Tendsto z atTop (𝓝 p)) (hW : Tendsto (fun k => Cert.W (z k)) atTop (𝓝 0)) :
    False := by
  obtain ⟨G, hG, hbound⟩ := convex_gradient_bound_on_compact hF (isCompact_closedBall p 1)
  have hnear : ∀ᶠ k in atTop, z k ∈ Metric.closedBall p 1 :=
    hzp.eventually (Metric.closedBall_mem_nhds p one_pos)
  have hcoord : ∀ᶠ k in atTop, ∀ i, |h k i| ≤ G := by
    filter_upwards [hnear] with k hk i
    have hs := hbound (z k) hk (h k) (hh k)
    have hi : (h k i) ^ 2 ≤ sqNorm (h k) := by
      unfold sqNorm
      exact Finset.single_le_sum (f := fun j => (h k j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have : (h k i) ^ 2 ≤ G ^ 2 := hi.trans hs
    rcases abs_le_of_sq_le_sq' this hG.le with ⟨h1, h2⟩
    exact abs_le.mpr ⟨h1, h2⟩
  have hentry : ∀ i j, Tendsto (fun k => Cert.W (z k) i j) atTop (𝓝 0) := fun i j =>
    ((hW.apply_nhds i).apply_nhds j)
  have hsum : Tendsto (fun k => ∑ i, ∑ j, G * |Cert.W (z k) i j| * G) atTop (𝓝 0) := by
    have : Tendsto (fun k => ∑ i, ∑ j, G * |Cert.W (z k) i j| * G) atTop
        (𝓝 (∑ i : Fin n, ∑ j : Fin n, G * |(0 : ℝ)| * G)) := by
      apply tendsto_finset_sum
      intro i _
      apply tendsto_finset_sum
      intro j _
      exact ((hentry i j).abs.const_mul G).mul_const G
    simpa using this
  have hle : ∀ᶠ k in atTop, metricEnergy (Cert.W (z k)) (h k) ≤
      ∑ i, ∑ j, G * |Cert.W (z k) i j| * G := by
    filter_upwards [hcoord] with k hk
    unfold metricEnergy dot
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    calc ∑ i, ∑ j, h k i * (Cert.W (z k) i j * h k j)
        ≤ ∑ i, ∑ j, |h k i * (Cert.W (z k) i j * h k j)| :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => le_abs_self _
      _ ≤ ∑ i, ∑ j, G * |Cert.W (z k) i j| * G := by
          apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
          rw [abs_mul, abs_mul]
          have h1 := hk i
          have h2 := hk j
          have h3 := abs_nonneg (Cert.W (z k) i j)
          calc |h k i| * (|Cert.W (z k) i j| * |h k j|)
              ≤ G * (|Cert.W (z k) i j| * G) := by
                apply mul_le_mul h1 _ (by positivity) hG.le
                exact mul_le_mul_of_nonneg_left h2 h3
            _ = G * |Cert.W (z k) i j| * G := by ring
  have hm : ∀ k, Cert.m ≤ metricEnergy (Cert.W (z k)) (h k) := fun k =>
    Cert.visibility (z k) (hz k) (h k) (hh k)
  have hlim : Cert.m ≤ 0 := ge_of_tendsto hsum (by
    filter_upwards [hle] with k hk
    exact (hm k).trans hk)
  linarith [Cert.m_pos]

/-- If an accessible jump exists at $p$ and the accessible jumps span the whole space, no band
certificate has a finite continuous extension to $p$: the extension would vanish
(`spanning_jumps_no_direction`), contradicting visibility along an accessible sequence
(`no_vanishing_limit`). -/
theorem spanning_jumps_obstruction {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η) (p : Vec n)
    (hne : ∃ j, AccessibleJump F K Fstar c₁ c₂ η p j)
    (hspan : accessibleSpan F K Fstar c₁ c₂ η p = ⊤) :
    ∀ Cert : BandCertificate F K Fstar c₁ c₂ η, ¬ ∃ Wp : Mat n,
      Tendsto Cert.W (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p)
        (𝓝 Wp) := by
  rintro Cert ⟨Wp, hext⟩
  have hW0 := (spanning_jumps_no_direction hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp
    hext hspan).1
  obtain ⟨j, x, z, g, h, hp, _hx, hz, _hd, _ht, _hy⟩ := hne
  have hW := field_limit Cert.W p Wp hext x z g h hp hz
  rw [hW0] at hW
  exact no_vanishing_limit hF Cert p z h (fun k => (hp k).2.1)
    (fun k => (hp k).2.2.gradient_z) hz hW

/-- Item `C/05_G/prose/050` (`companion/chapters/05_G.tex:225`): "At a generic
two-dimensional vertex with independent accessible jumps in both coordinates, there may be no
remaining comparison direction." Obstruction form, as the next sentence reads it ("The
common-target obstruction above makes that interpretation rigorous without continuity of a
certificate"): at a point $p$ of the plane with two linearly independent accessible limiting
jumps, no band certificate has a finite continuous extension to $p$; such an extension would
vanish at $p$ (`vertex_no_direction`), contradicting visibility near $p$
(`no_vanishing_limit`). Such vertices exist: the example at the end of the module
($|u|+|v|+(u-1)^2$ at $(0,0)$). -/
theorem vertex_obstruction {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec 2))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η) (p j₁ j₂ : Vec 2)
    (hj₁ : AccessibleJump F K Fstar c₁ c₂ η p j₁) (hj₂ : AccessibleJump F K Fstar c₁ c₂ η p j₂)
    (hind : LinearIndependent ℝ ![euclideanVector j₁, euclideanVector j₂]) :
    ∀ Cert : BandCertificate F K Fstar c₁ c₂ η, ¬ ∃ Wp : Mat 2,
      Tendsto Cert.W (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p)
        (𝓝 Wp) := by
  rintro Cert ⟨Wp, hext⟩
  have hW0 := (vertex_no_direction hF Fstar hFstar b K hK_def hK c₁ c₂ hc η hη Cert p Wp hext
    j₁ j₂ hj₁ hj₂ hind).1
  obtain ⟨x, z, g, h, hp, _hx, hz, _hd, _ht, _hy⟩ := hj₁
  have hW := field_limit Cert.W p Wp hext x z g h hp hz
  rw [hW0] at hW
  exact no_vanishing_limit hF Cert p z h (fun k => (hp k).2.1)
    (fun k => (hp k).2.2.gradient_z) hz hW

/-! ### Section 5.6: in one dimension the condition can be fully eliminated (lines 234-257) -/

/-- Item `C/05_G/proposition/003` (`companion/chapters/05_G.tex:236-246`), Proposition 5.6.1 (Exact
scalar characterization), with displays `G:eq:scalar` (`disp/023`) and `disp/024`. On a compact
positive objective band in $\R$ ($F:\R^1\to\R$ finite convex, $F_*=\min F$,
$K=\{F\le b\}$ compact, $\eta>0$, $0<c_1<c_2<1$), the transported certificate exists if and
only if, for some small-decrease threshold $\delta>0$, the eligible pairs in $K_\eta$ with
$d\le\delta$ satisfy
\[ \sup_{(x,z)}\frac{|F'(z)-F'(x)|}{|z-x|\,|F'(z)|^2}<\infty; \]
equivalently, $|F'(z)-F'(x)|\le A_\eta|z-x|$ on these eligible pairs (not on all pairs). -/
theorem exact_scalar_characterization {F : Vec 1 → ℝ} (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec 1))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η) (Kη : Set (Vec 1))
    (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) :
    (Nonempty (BandCertificate F K Fstar c₁ c₂ η) ↔
      ∃ δ : ℝ, 0 < δ ∧ BddAbove {q : ℝ | ∃ x z g h : Vec 1, x ∈ Kη ∧ z ∈ Kη ∧
        EligiblePair F c₁ c₂ x z g h ∧ -dot g (z - x) ≤ δ ∧
        q = |h 0 - g 0| / (|z 0 - x 0| * |h 0| ^ 2)}) ∧
    (Nonempty (BandCertificate F K Fstar c₁ c₂ η) ↔
      ∃ δ : ℝ, 0 < δ ∧ ∃ A : ℝ, ∀ x ∈ Kη, ∀ z ∈ Kη, ∀ g h : Vec 1,
        EligiblePair F c₁ c₂ x z g h → -dot g (z - x) ≤ δ → |h 0 - g 0| ≤ A * |z 0 - x 0|) := by
  obtain ⟨xs, hxs⟩ := hFstar.1
  subst hxs hKη
  have _ := hK_def
  refine ⟨(scalar_certificate_iff_quotient hF xs hc.2.2 hη).trans ⟨?_, ?_⟩,
    (scalar_certificate_iff_eligible_lipschitz (c₁ := c₁) hF xs hK hc.2.2 hη).trans
      ⟨fun ⟨δ, hδ, A, hA⟩ => ⟨δ, hδ, A, fun x hx z hz g h hp hd => hA x z g h hx hz hp hd⟩,
        fun ⟨δ, hδ, A, hA⟩ => ⟨δ, hδ, A, fun x z g h hx hz hp hd => hA x hx z hz g h hp hd⟩⟩⟩
  · rintro ⟨δ, hδ, A, hA⟩
    refine ⟨δ, hδ, A, ?_⟩
    rintro q ⟨x, z, g, h, hx, hz, hp, hd, rfl⟩
    rw [sq_abs]
    exact hA x z g h hx hz hp hd
  · rintro ⟨δ, hδ, A, hA⟩
    refine ⟨δ, hδ, A, fun x z g h hx hz hp hd => ?_⟩
    have := hA ⟨x, z, g, h, hx, hz, hp, hd, rfl⟩
    rwa [sq_abs] at this

/-- Item `C/05_G/prose/052` (`companion/chapters/05_G.tex:255`): "This reveals a genuine
restriction: an eligible arbitrarily small crossing of a nonoptimal derivative jump rules out
every certificate." In the setting of the Proposition (Exact scalar characterization): let the
scalar function $f(t)=F(t)$ have one-sided derivatives $f'_-(a)=l<r=f'_+(a)$ at a nonoptimal
point $a$; if for every $\varepsilon>0$ some eligible pair in $K_\eta$ with $d\le\varepsilon$ and
$|z-x|\le\varepsilon$ crosses $a$, there is no certificate on $K_\eta$. -/
theorem small_crossing_no_certificate {F : Vec 1 → ℝ} (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec 1))
    (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (η : ℝ) (hη : 0 < η) (Kη : Set (Vec 1))
    (hKη : Kη = {x | x ∈ K ∧ F x ≥ Fstar + η}) (a l r : ℝ)
    (_ha : Fstar < F (OneDimensional.embed a))
    (hl : HasDerivWithinAt (fun t => F (OneDimensional.embed t)) l (Iio a) a)
    (hr : HasDerivWithinAt (fun t => F (OneDimensional.embed t)) r (Ioi a) a) (hlr : l < r)
    (hcross : ∀ ε : ℝ, 0 < ε → ∃ x z g h : Vec 1, x ∈ Kη ∧ z ∈ Kη ∧
      EligiblePair F c₁ c₂ x z g h ∧ -dot g (z - x) ≤ ε ∧ |z 0 - x 0| ≤ ε ∧
      ((x 0 < a ∧ a < z 0) ∨ (z 0 < a ∧ a < x 0))) :
    ¬ Nonempty (BandCertificate F K Fstar c₁ c₂ η) := by
  intro hcert
  obtain ⟨δ, hδ, A, hA⟩ := (exact_scalar_characterization hF Fstar hFstar b K hK_def hK c₁ c₂
    hc η hη Kη hKη).2.mp hcert
  have hf : ConvexOn ℝ univ (fun t => F (OneDimensional.embed t)) := by
    simpa only [Set.preimage_univ, Function.comp_def] using
      hF.comp_linearMap OneDimensional.embed.toLinearMap
  set ε := min δ ((r - l) / (2 * (|A| + 1))) with hε_def
  have hJ : 0 < r - l := sub_pos.mpr hlr
  have hε : 0 < ε := lt_min hδ (div_pos hJ (by positivity))
  obtain ⟨x, z, g, h, hx, hz, hp, hd, hs, hcr⟩ := hcross ε hε
  have hgx := scalar_derivative hp.gradient_x
  have hhz := scalar_derivative hp.gradient_z
  have hjump : r - l ≤ |h 0 - g 0| := by
    rcases hcr with ⟨hxa, haz⟩ | ⟨hza, hax⟩
    · have h1 := hf.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hxa hgx
      have h2 := hf.slope_le_of_hasDerivWithinAt_Iio (mem_univ _) (mem_univ _) hxa hl
      have h3 := hf.le_slope_of_hasDerivWithinAt_Ioi (mem_univ _) (mem_univ _) haz hr
      have h4 := hf.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) haz hhz
      have : r - l ≤ h 0 - g 0 := by linarith
      exact this.trans (le_abs_self _)
    · have h1 := hf.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hza hhz
      have h2 := hf.slope_le_of_hasDerivWithinAt_Iio (mem_univ _) (mem_univ _) hza hl
      have h3 := hf.le_slope_of_hasDerivWithinAt_Ioi (mem_univ _) (mem_univ _) hax hr
      have h4 := hf.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hax hgx
      have : r - l ≤ g 0 - h 0 := by linarith
      rw [abs_sub_comm]
      exact this.trans (le_abs_self _)
  have hlip := hA x hx z hz g h hp (hd.trans (min_le_left _ _))
  have hsε : |z 0 - x 0| ≤ (r - l) / (2 * (|A| + 1)) := hs.trans (min_le_right _ _)
  have hA1 : A * |z 0 - x 0| ≤ |A| * |z 0 - x 0| :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (abs_nonneg _)
  have hA2 : |A| * |z 0 - x 0| ≤ |A| * ((r - l) / (2 * (|A| + 1))) :=
    mul_le_mul_of_nonneg_left hsε (abs_nonneg A)
  have hA3 : |A| * ((r - l) / (2 * (|A| + 1))) < r - l := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg A]
  linarith

/-! ### Section 5.6.1: convergence does not need the scalar restriction (lines 260-284) -/

/-- Item `C/05_G/proposition/G:prop:scalarconv` (`companion/chapters/05_G.tex:263-265`),
Proposition 5.6.2 = `G:prop:scalarconv` (Scalar convergence, independently of BFGS updates). Let
$f:\R\to\R$ be finite and convex with unique minimizer $x_*$ and compact initial sublevel. Every
infinite differentiable-iterate Armijo--weak-Wolfe run using any positive scalar metric
($x_{k+1}=x_k-\alpha_kM_kg_k$ with $g_k=f'(x_k)\ne0$, $M_k>0$, $\alpha_k>0$,
$0<c_1<c_2<1$) converges to $x_*$ (values and iterates). Full BFGS in dimension one is such a
run (`scalar_bfgs_convergence`). -/
theorem scalar_convergence {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (xstar : ℝ)
    (hmin : ∀ x, f xstar ≤ f x) (huniq : ∀ x, f x = f xstar → x = xstar)
    (x g M α : ℕ → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (hM : ∀ k, 0 < M k) (hα : ∀ k, 0 < α k) (hg : ∀ k, g k ≠ 0)
    (hderiv : ∀ k, HasDerivAt f (g k) (x k))
    (hstep : ∀ k, x (k + 1) = x k - α k * M k * g k)
    (harmijo : ∀ k, f (x (k + 1)) ≤ f (x k) + c₁ * g k * (x (k + 1) - x k))
    (hwolfe : ∀ k, g (k + 1) * (x (k + 1) - x k) ≥ c₂ * g k * (x (k + 1) - x k))
    (hK : IsCompact {y | f y ≤ f (x 0)}) :
    Tendsto (fun k => f (x k)) atTop (𝓝 (f xstar)) ∧ Tendsto x atTop (𝓝 xstar) :=
  let R : ScalarMetricRun f :=
    { convex := hf, x := x, g := g, metric := M, α := α, c₁ := c₁, c₂ := c₂, c₁_pos := hc₁,
      c₁_lt_c₂ := hc₁₂, c₂_lt_one := hc₂, metric_pos := hM, alpha_pos := hα, gradient_ne := hg,
      hasDeriv := hderiv, step := hstep, armijo := harmijo, weak_wolfe := hwolfe }
  R.convergence hK xstar hmin huniq

/-- Proposition `G:prop:scalarconv` for actual full BFGS in dimension one: every admissible run
on a finite convex $F:\R^1\to\R$ with unique minimizer and compact initial sublevel converges. -/
theorem scalar_bfgs_convergence {F : Vec 1 → ℝ} (R : AdmissibleBFGSRun 1 F)
    (hK : IsCompact {y | F y ≤ F (R.x 0)}) (xstar : Vec 1) (hmin : ∀ x, F xstar ≤ F x)
    (huniq : ∀ x, F x = F xstar → x = xstar) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧ Tendsto R.x atTop (𝓝 xstar) :=
  R.scalar_convergence hK xstar hmin huniq

open ScalarCounterexamples OneDimensional in
/-- The existential reading of item `C/05_G/prose/053` (line 269) as printed before its
correction of 15 October 2026 (M22; "Already $f(x)=\frac12(x+2)^2+|x|$ gives a finite strongly
convex example with global convergence but no global certificate on a sublevel containing
zero"): $f$ is $1$-strongly
convex with unique minimizer $-1$; every admissible run converges to it; and with
$(c_1,c_2)=(1/4,1/2)$ (lines 277-278) the sublevel $\{f\le3\}$ contains $0$ but carries no band
certificates. Read for every sublevel containing zero the claim fails at $\{f\le2\}$
(`two_sublevel_counterexample`); corrected: `shifted_global_nonnecessity_interior`. -/
theorem shifted_global_nonnecessity :
    StrongConvexOn univ 1 shiftedAbs ∧ (∀ x, shiftedAbs (-1) ≤ shiftedAbs x) ∧
      (∀ x, shiftedAbs x = shiftedAbs (-1) → x = -1) ∧
      (∀ R : AdmissibleBFGSRun 1 shiftedObjective,
        Tendsto (fun k => shiftedObjective (R.x k)) atTop (𝓝 (3 / 2)) ∧
          Tendsto R.x atTop (𝓝 (embed (-1)))) ∧
      (0 : Vec 1) ∈ {x | shiftedObjective x ≤ 3} ∧
      ¬ HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) :=
  ⟨shiftedAbs_strongConvex, shiftedAbs_minimum, shiftedAbs_unique, shifted_actual_bfgs_converges,
    by norm_num [shiftedObjective, shiftedAbs], shifted_no_band_certificates⟩

open ScalarCounterexamples OneDimensional in
/-- Every differentiable point of the sublevel $\{f\le2\}=[-2,0]$ of $f(x)=\frac12(x+2)^2+|x|$
is negative. -/
theorem two_sublevel_neg {x : Vec 1} (hx : shiftedObjective x ≤ 2) {g : Vec 1}
    (hg : HasFDerivAt shiftedObjective (gradientFunctional g) x) : x 0 < 0 := by
  have hne := ShiftedAbsAccessibility.actual_endpoint_ne_zero hg
  rcases lt_or_gt_of_ne hne with h | h
  · exact h
  · exfalso
    simp only [shiftedObjective, shiftedAbs, embed_apply, abs_of_pos h] at hx
    nlinarith

open ScalarCounterexamples OneDimensional in
/-- Band certificates on $\{f\le2\}$ for all constants (construction of the independent
review): $W=I$, $m=2\eta$, $C=1$, $L=0$, $\delta=1$; every differentiable band point is $<0$,
where $f(x)=\frac12(x+1)^2+\frac32$. -/
def twoCert (c₁ c₂ η : ℝ) (hη : 0 < η) :
    BandCertificate shiftedObjective {x | shiftedObjective x ≤ 2}
      (shiftedObjective (embed (-1))) c₁ c₂ η where
  W := fun _ => 1
  m := 2 * η
  C := 1
  L := 0
  δ := 1
  m_pos := by linarith
  L_nonneg := le_rfl
  delta_pos := one_pos
  positive_semidefinite := fun _ _ _ => Matrix.PosSemidef.one
  visibility := fun x hx g hg => by
    have hx0 : x 0 < 0 := two_sublevel_neg hx.1 hg
    have hgx := ShiftedAbsAccessibility.actual_gradient_neg hg hx0
    have hb := hx.2
    simp only [shiftedObjective, shiftedAbs, embed_apply, abs_of_neg hx0] at hb
    rw [scalar_energy, hgx]
    norm_num at hb ⊢
    nlinarith
  secant := fun x z g h hx hz hp _ => by
    have hx0 : x 0 < 0 := two_sublevel_neg hx.1 hp.gradient_x
    have hz0 : z 0 < 0 := two_sublevel_neg hz.1 hp.gradient_z
    have hgx := ShiftedAbsAccessibility.actual_gradient_neg hp.gradient_x hx0
    have hhz := ShiftedAbsAccessibility.actual_gradient_neg hp.gradient_z hz0
    rw [scalar_energy]
    simp only [pairCurvature, pairStep, dot, Fin.sum_univ_one, Pi.sub_apply, hgx, hhz,
      Matrix.one_apply_eq]
    nlinarith [sq_nonneg (z 0 - x 0)]
  transport := fun x z g h _ _ hp _ => by
    have hs : pairStep x z ≠ 0 := by
      intro h0
      have := hp.decrease_pos
      simp [pairDecrease, h0, dot] at this
    rw [BfgsCoverage.Article.Energy.stepProjector_one_dim hs]
    simpa using Matrix.PosSemidef.zero

open ScalarCounterexamples OneDimensional in
/-- Counterexample to item `C/05_G/prose/053` (line 269) as printed before its correction of 15
October 2026 (M22; "... no global certificate on a sublevel containing zero"), read for every
sublevel containing zero:
$\{f\le2\}=[-2,0]$ is compact and contains $0$ (on its boundary), yet it carries the band
certificates for $(c_1,c_2)=(1/4,1/2)$ (`twoCert`; due to the independent review). -/
theorem two_sublevel_counterexample :
    (0 : Vec 1) ∈ {x | shiftedObjective x ≤ 2} ∧ IsCompact {x | shiftedObjective x ≤ 2} ∧
      HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ 2}
        (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) :=
  ⟨by norm_num [shiftedObjective, shiftedAbs], shiftedObjective_sublevel_compact 2,
    fun η hη _ => ⟨twoCert _ _ η hη⟩⟩

open ScalarCounterexamples OneDimensional in
/-- For every sublevel $\{f\le b\}$ with $b>2$ (zero in its interior) the band $\eta=1/4$ has no
band certificate for $(c_1,c_2)=(1/4,1/2)$, so $\{f\le b\}$ does not carry the band certificates
(proof of the independent review, from the eligible crossing pairs $(\varepsilon,-\varepsilon/2)$
and the scalar characterization). -/
theorem interior_sublevel_no_certificate (b : ℝ) (hb : 2 < b) :
    ¬ Nonempty (BandCertificate shiftedObjective {x | shiftedObjective x ≤ b}
      (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) (1 / 4)) ∧
    ¬ HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ b}
      (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) := by
  have hm : shiftedObjective (embed (-1)) = 3 / 2 := by norm_num [shiftedObjective, shiftedAbs]
  have hband : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 8 → ε ≤ (b - 2) / 4 →
      crossingX ε ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ b}
        (shiftedObjective (embed (-1))) (1 / 4) ∧
      crossingZ ε ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ b}
        (shiftedObjective (embed (-1))) (1 / 4) := by
    intro ε hε h8 hb4
    have hv := crossing_values hε
    simp only [positiveBand, Set.mem_setOf_eq]
    rw [hm, hv.1, hv.2]
    have he2 : ε ^ 2 ≤ ε / 8 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr h8)]
    constructor <;> constructor <;> nlinarith [sq_nonneg ε]
  have hnot : ¬ Nonempty (BandCertificate shiftedObjective {x | shiftedObjective x ≤ b}
      (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) (1 / 4)) := by
    intro hc
    obtain ⟨δ, hδ, A, hA⟩ := (scalar_certificate_iff_eligible_lipschitz shiftedObjective_convex
      (embed (-1)) (shiftedObjective_sublevel_compact b) (by norm_num) (by norm_num)).mp hc
    set ε : ℝ := min (min (1 / 8) ((b - 2) / 4)) (min (δ / 10) (1 / (|A| + 1))) with hεdef
    have hε : 0 < ε := by
      apply lt_min (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) (by positivity))
    have h8 : ε ≤ 1 / 8 := (min_le_left _ _).trans (min_le_left _ _)
    have hb4 : ε ≤ (b - 2) / 4 := (min_le_left _ _).trans (min_le_right _ _)
    have hδ10 : ε ≤ δ / 10 := (min_le_right _ _).trans (min_le_left _ _)
    have hA1 : ε ≤ 1 / (|A| + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have hbd := hband ε hε h8 hb4
    have hdec : pairDecrease (crossingX ε) (crossingZ ε) (crossingG ε) ≤ δ := by
      rw [crossing_decrease]; nlinarith
    have he := hA _ _ _ _ hbd.1 hbd.2 (crossing_eligible hε) hdec
    have hy : 1 - ε / 2 - (3 + ε) < 0 := by linarith
    have hs : -ε / 2 - ε < 0 := by linarith
    simp only [crossingX, crossingZ, crossingG, crossingH, embed_apply,
      abs_of_neg hy, abs_of_neg hs] at he
    have hAe : |A| * ε ≤ 1 := by
      have hpos : (0 : ℝ) < |A| + 1 := by positivity
      have := mul_le_mul_of_nonneg_left hA1 (abs_nonneg A)
      calc |A| * ε ≤ |A| * (1 / (|A| + 1)) := this
        _ ≤ 1 := by rw [mul_one_div, div_le_one hpos]; linarith
    have hAA : A * (-(-ε / 2 - ε)) ≤ |A| * (3 / 2 * ε) := by
      have : -(-ε / 2 - ε) = 3 / 2 * ε := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    nlinarith
  have hε0 : 0 < min (1 / 8) ((b - 2) / 4) := lt_min (by norm_num) (by linarith)
  exact ⟨hnot, fun h => hnot (h (1 / 4) (by norm_num)
    ⟨crossingX (min (1 / 8) ((b - 2) / 4)), (hband _ hε0 (min_le_left _ _)
      (min_le_right _ _)).1⟩)⟩

open ScalarCounterexamples OneDimensional in
/-- $0$ lies in the interior of the sublevel $\{f\le b\}$ exactly when $b>f(0)=2$. -/
theorem zero_mem_interior_iff (b : ℝ) :
    (0 : Vec 1) ∈ interior {x | shiftedObjective x ≤ b} ↔ 2 < b := by
  have hcont : Continuous shiftedObjective :=
    continuous_iff_continuousOn_univ.mpr (shiftedObjective_convex.continuousOn isOpen_univ)
  constructor
  · intro h
    rw [mem_interior_iff_mem_nhds] at h
    have ht : Tendsto (fun t : ℝ => embed t) (𝓝[>] 0) (𝓝 (0 : Vec 1)) := by
      have := (embed.continuous.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa using this
    obtain ⟨t, ht1, ht2⟩ := ((ht.eventually h).and self_mem_nhdsWithin).exists
    have ht2' : 0 < t := ht2
    simp only [Set.mem_setOf_eq, shiftedObjective, shiftedAbs, embed_apply,
      abs_of_pos ht2'] at ht1
    nlinarith
  · intro hb
    refine mem_interior.mpr ⟨{x | shiftedObjective x < b},
      fun x (hx : shiftedObjective x < b) => show shiftedObjective x ≤ b from le_of_lt hx,
      isOpen_lt hcont continuous_const, ?_⟩
    show shiftedObjective 0 < b
    norm_num [shiftedObjective, shiftedAbs]
    linarith

open ScalarCounterexamples OneDimensional in
/-- Item `C/05_G/prose/053` (`companion/chapters/05_G.tex:269`), as corrected on 15 October 2026
(M22): "Already $f(x)=\frac12(x+2)^2+|x|$ gives a finite strongly convex example with
global convergence but, for $(c_1,c_2)=(1/4,1/2)$, no global certificate on any sublevel
containing zero in its interior." $f$ is $1$-strongly convex with unique minimizer $-1$, every
admissible run converges to it, and no sublevel $\{f\le b\}$ with $0$ in its interior carries
the band certificates for $(1/4,1/2)$. -/
theorem shifted_global_nonnecessity_interior :
    StrongConvexOn univ 1 shiftedAbs ∧ (∀ x, shiftedAbs (-1) ≤ shiftedAbs x) ∧
      (∀ x, shiftedAbs x = shiftedAbs (-1) → x = -1) ∧
      (∀ R : AdmissibleBFGSRun 1 shiftedObjective,
        Tendsto (fun k => shiftedObjective (R.x k)) atTop (𝓝 (3 / 2)) ∧
          Tendsto R.x atTop (𝓝 (embed (-1)))) ∧
      ∀ b : ℝ, (0 : Vec 1) ∈ interior {x | shiftedObjective x ≤ b} →
        ¬ HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ b}
          (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) :=
  ⟨shiftedAbs_strongConvex, shiftedAbs_minimum, shiftedAbs_unique, shifted_actual_bfgs_converges,
    fun b hb => (interior_sublevel_no_certificate b ((zero_mem_interior_iff b).mp hb)).2⟩

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/disp/025` (`companion/chapters/05_G.tex:270-272`): "For $x=\epsilon$,
$z=-\epsilon/2$ with $\epsilon>0$," (line 269; "with $\epsilon>0$" added on 15 October 2026,
wording point W16)
\[ g_x=3+\varepsilon,\quad g_z=1-\varepsilon/2,\quad y=-2-3\varepsilon/2, \]
for the gradients $g_x,g_z$ of $f$ at these points (they exist: `crossing_gradients`). -/
theorem shifted_crossing_gradients (ε : ℝ) (hε : 0 < ε) (gx gz y : Vec 1)
    (hgx : HasFDerivAt shiftedObjective (gradientFunctional gx) (embed ε))
    (hgz : HasFDerivAt shiftedObjective (gradientFunctional gz) (embed (-ε / 2)))
    (hy : y = gz - gx) :
    gx 0 = 3 + ε ∧ gz 0 = 1 - ε / 2 ∧ y 0 = -2 - 3 * ε / 2 := by
  have h1 := actual_gradient_pos hgx (by simpa using hε)
  have h2 := actual_gradient_neg hgz (by simp; linarith)
  simp only [embed_apply] at h1 h2
  refine ⟨by linarith, by linarith, ?_⟩
  rw [hy, Pi.sub_apply, h1, h2]
  ring

open ScalarCounterexamples OneDimensional ShiftedAbsAccessibility in
/-- Item `C/05_G/disp/026` (`companion/chapters/05_G.tex:273-277`): for the same pairs,
\[ d=\tfrac92\varepsilon+\tfrac32\varepsilon^2,\quad
   \Delta=\tfrac72\varepsilon+\tfrac38\varepsilon^2,\quad t=3\varepsilon+\tfrac94\varepsilon^2. \] -/
theorem shifted_crossing_quantities (ε : ℝ) (hε : 0 < ε) (gx gz : Vec 1)
    (hgx : HasFDerivAt shiftedObjective (gradientFunctional gx) (embed ε))
    (hgz : HasFDerivAt shiftedObjective (gradientFunctional gz) (embed (-ε / 2)))
    (s y : Vec 1) (hs : s = embed (-ε / 2) - embed ε) (hy : y = gz - gx) (d Δ t : ℝ)
    (hd : d = -dot gx s) (hΔ : Δ = shiftedObjective (embed ε) - shiftedObjective (embed (-ε / 2)))
    (ht : t = dot y s) :
    d = 9 / 2 * ε + 3 / 2 * ε ^ 2 ∧ Δ = 7 / 2 * ε + 3 / 8 * ε ^ 2 ∧
      t = 3 * ε + 9 / 4 * ε ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := shifted_crossing_gradients ε hε gx gz y hgx hgz hy
  have hv := crossing_values hε
  simp only [crossingX, crossingZ] at hv
  refine ⟨?_, ?_, ?_⟩
  · rw [hd, hs]
    simp only [dot, Fin.sum_univ_one, Pi.sub_apply, embed_apply, h1]
    ring
  · rw [hΔ, hv.1, hv.2]
    ring
  · rw [ht, hs]
    simp only [dot, Fin.sum_univ_one, Pi.sub_apply, embed_apply, h3]
    ring

open ScalarCounterexamples OneDimensional in
/-- Item `C/05_G/prose/054` (`companion/chapters/05_G.tex:278`): "These pairs are strictly
eligible for $(1/4,1/2)$ for small $\varepsilon$, and their scalar quotient in
\eqref{G:eq:scalar} diverges." For $\varepsilon>0$ near $0$: $d>0$,
$\frac14d<\Delta<d$, $t>(1-\frac12)d$ (strict eligibility), and
$|g_z-g_x|/(|z-x|\,|g_z|^2)\to\infty$ as $\varepsilon\downarrow0$. -/
theorem shifted_crossing_eligible_divergent :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      EligiblePair shiftedObjective (1 / 4) (1 / 2) (embed ε) (embed (-ε / 2)) (embed (3 + ε))
          (embed (1 - ε / 2)) ∧
        0 < -dot (embed (3 + ε)) (embed (-ε / 2) - embed ε) ∧
        1 / 4 * -dot (embed (3 + ε)) (embed (-ε / 2) - embed ε) <
          shiftedObjective (embed ε) - shiftedObjective (embed (-ε / 2)) ∧
        shiftedObjective (embed ε) - shiftedObjective (embed (-ε / 2)) <
          -dot (embed (3 + ε)) (embed (-ε / 2) - embed ε) ∧
        (1 - 1 / 2) * -dot (embed (3 + ε)) (embed (-ε / 2) - embed ε) <
          dot (embed (1 - ε / 2) - embed (3 + ε)) (embed (-ε / 2) - embed ε)) ∧
    Tendsto (fun ε : ℝ => |(1 - ε / 2) - (3 + ε)| / (|(-ε / 2) - ε| * |1 - ε / 2| ^ 2))
      (𝓝[>] 0) atTop := by
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ⟨crossing_eligible hε, crossing_strict hε⟩
  · refine crossing_quotient_tendsto.congr fun ε => ?_
    simp only [crossingH, crossingG, crossingZ, crossingX, embed_apply, sq_abs]

/-- An admissible run on $f(x)=\frac12(x+2)^2+|x|$ (non-vacuity): $x_k=-1-2^{-k}$, $H_k=1$,
$\alpha_k=1/2$, $(c_1,c_2)=(1/4,1/2)$; on $x<0$, $f(x)=\frac12(x+1)^2+\frac32$. -/
def shiftedRun : AdmissibleBFGSRun 1 ScalarCounterexamples.shiftedObjective :=
  BfgsCoverage.Article.Global.oneDimRun ScalarCounterexamples.shiftedObjective
    ScalarCounterexamples.shiftedObjective_convex (fun k => -1 - (1 / 2) ^ k)
    (fun k => -(1 / 2) ^ k) (fun _ => 1) (fun _ => 1 / 2) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) one_pos (fun _ => by norm_num)
    (fun k => neg_ne_zero.mpr (pow_ne_zero k (by norm_num)))
    (fun k => by
      have hneg : -1 - (1 / 2 : ℝ) ^ k < 0 := by
        have : (0 : ℝ) < (1 / 2) ^ k := by positivity
        linarith
      have h := ScalarCounterexamples.coordinate_hasGradient
        (ScalarCounterexamples.shiftedAbs_hasDerivAt_neg hneg)
      have he : -1 - (1 / 2 : ℝ) ^ k + 1 = -(1 / 2) ^ k := by ring
      rw [he] at h
      exact h)
    (fun k => by
      dsimp only
      rw [pow_succ (1 / 2 : ℝ) k]
      ring)
    (fun k => by
      dsimp only
      have : (0 : ℝ) < (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      have : (0 : ℝ) < (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      have hp : (0 : ℝ) < (1 / 2) ^ k := by positivity
      have hnum : -1 - (1 / 2 : ℝ) ^ (k + 1) - (-1 - (1 / 2) ^ k) =
          -(1 / 2) ^ (k + 1) - -(1 / 2) ^ k := by ring
      rw [hnum, div_self]
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      have hp : (0 : ℝ) < (1 / 2) ^ k := by positivity
      have h1 : -1 - (1 / 2 : ℝ) ^ (k + 1) < 0 := by
        have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
        linarith
      have h0 : -1 - (1 / 2 : ℝ) ^ k < 0 := by linarith
      simp only [ScalarCounterexamples.shiftedObjective, ScalarCounterexamples.shiftedAbs,
        OneDimensional.embed_apply, abs_of_neg h1, abs_of_neg h0]
      rw [pow_succ (1 / 2 : ℝ) k]
      nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ k)])
    (fun k => by
      dsimp only
      rw [pow_succ (1 / 2 : ℝ) k]
      nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ k)])

/-! ### Section 5.7: local nonexistence despite global convergence (lines 287-329) -/

open AccumulatingKinks in
/-- Item `C/05_G/disp/027` (`companion/chapters/05_G.tex:292-294`), equation `G:eq:infinite`:
$a_j=4^{-j}$ ($j\ge1$) and
\[ h(x)=\frac12x^2+3\sum_{j=1}^\infty a_j(x-a_j)_+. \]
The library's `AccumulatingKinks.objective` (with `coordinateObjective x = h(x_0)` on $\R^1$)
indexes the knots from $0$: `knot j` $=a_{j+1}=(1/4)^{j+1}$, and $(u)_+=\max(u,0)$. -/
theorem h_def :
    (∀ x : ℝ, objective x =
      x ^ 2 / 2 + 3 * ∑' j : ℕ, (1 / 4 : ℝ) ^ (j + 1) * max (x - (1 / 4 : ℝ) ^ (j + 1)) 0) ∧
    (∀ j : ℕ, knot j = (4 : ℝ)⁻¹ ^ (j + 1)) ∧ (∀ x : Vec 1, coordinateObjective x = objective (x 0)) :=
  ⟨fun _ => rfl, fun j => by rw [knot, one_div], fun _ => rfl⟩

/-- The knots $a_j=(1/4)^j$, $j\ge1$, are the library's `knot (j-1)`. -/
theorem knot_of_index (j : ℕ) (hj : 1 ≤ j) :
    (1 / 4 : ℝ) ^ j = AccumulatingKinks.knot (j - 1) := by
  rw [AccumulatingKinks.knot, Nat.sub_add_cancel hj]

open AccumulatingKinks in
/-- Item `C/05_G/prose/056` (`companion/chapters/05_G.tex:295`): "The series converges
uniformly on compact sets: its absolute value is bounded by a constant times $\sum a_j$." On every
compact $K$ the partial sums converge uniformly, and $|\sum_ja_j(x-a_j)_+|\le R\sum_ja_j$ for
$x\in K$. -/
theorem series_uniform :
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun N x => ∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ (j + 1) * max (x - (1 / 4 : ℝ) ^ (j + 1)) 0)
      (fun x => ∑' j : ℕ, (1 / 4 : ℝ) ^ (j + 1) * max (x - (1 / 4 : ℝ) ^ (j + 1)) 0) atTop K) ∧
    (∀ K : Set ℝ, IsCompact K → ∃ R : ℝ, ∀ x ∈ K,
      |∑' j : ℕ, (1 / 4 : ℝ) ^ (j + 1) * max (x - (1 / 4 : ℝ) ^ (j + 1)) 0| ≤
        R * ∑' j : ℕ, (1 / 4 : ℝ) ^ (j + 1)) := by
  refine ⟨fun K hK => series_uniform_on_compact hK, fun K hK => ?_⟩
  obtain ⟨R, _hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R, fun x hx => ?_⟩
  have hnn : 0 ≤ ∑' j : ℕ, term j x := tsum_nonneg fun j => term_nonneg j x
  have hle : ∑' j : ℕ, term j x ≤ ∑' j : ℕ, knot j * |x| :=
    (term_summable x).tsum_le_tsum (fun j => term_bound j x) (knot_summable.mul_right |x|)
  rw [tsum_mul_right] at hle
  have hx' : |x| ≤ R := by simpa only [Real.norm_eq_abs] using hbound x hx
  have hk : 0 ≤ ∑' j : ℕ, knot j := tsum_nonneg fun j => (knot_pos j).le
  change |∑' j : ℕ, term j x| ≤ R * ∑' j : ℕ, knot j
  rw [abs_of_nonneg hnn]
  nlinarith

open AccumulatingKinks in
/-- Item `C/05_G/prose/057` (`companion/chapters/05_G.tex:295`): "Every summand is convex,
and $h(x)\ge x^2/2$ with $h(0)=0$." -/
theorem h_basic :
    (∀ j : ℕ, ConvexOn ℝ univ fun x : ℝ => (1 / 4 : ℝ) ^ (j + 1) * max (x - (1 / 4 : ℝ) ^ (j + 1)) 0) ∧
      (∀ x, x ^ 2 / 2 ≤ objective x) ∧ objective 0 = 0 :=
  ⟨term_convex, objective_lower, objective_zero⟩

open AccumulatingKinks in
/-- Item `C/05_G/prose/058` (`companion/chapters/05_G.tex:295`): "Thus $h$ is finite,
$1$-strongly convex, coercive, and uniquely minimized at zero." The series converges at every
$x$ (so $h$ is real-valued), $h$ is $1$-strongly convex, $h(x)\to\infty$ as $|x|\to\infty$, and
$0$ is its unique minimizer. -/
theorem h_properties :
    (∀ x : ℝ, Summable fun j : ℕ => (1 / 4 : ℝ) ^ (j + 1) * max (x - (1 / 4 : ℝ) ^ (j + 1)) 0) ∧
      StrongConvexOn univ 1 objective ∧ Tendsto objective (cocompact ℝ) atTop ∧
      (∀ x, objective 0 ≤ objective x) ∧ (∀ x, objective x = objective 0 → x = 0) :=
  ⟨term_summable, objective_strongConvex, objective_coercive, objective_minimum, objective_unique⟩

open AccumulatingKinks in
/-- Item `C/05_G/prose/059` (`companion/chapters/05_G.tex:297`): "At a knot $a=a_j$, the
one-sided derivatives are $2a$ and $5a$." -/
theorem knot_one_sided (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    HasDerivWithinAt objective (2 * a) (Iic a) a ∧ HasDerivWithinAt objective (5 * a) (Ici a) a := by
  rw [ha, knot_of_index j hj]
  exact ⟨hasDerivWithinAt_knot_left (j - 1), hasDerivWithinAt_knot_right (j - 1)⟩

open AccumulatingKinks in
/-- Item `C/05_G/disp/028` (`companion/chapters/05_G.tex:298-300`): at a knot $a=a_j$, for
$a/4<x<a$,
\[ h(x)=\frac12x^2+ax-\frac15a^2. \] -/
theorem formula_below (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) (x : ℝ)
    (hlo : a / 4 < x) (hhi : x < a) : objective x = 1 / 2 * x ^ 2 + a * x - 1 / 5 * a ^ 2 := by
  rw [ha, knot_of_index j hj] at hlo hhi ⊢
  rw [objective_formula_below (j - 1) hlo.le hhi.le]
  ring

open AccumulatingKinks in
/-- On the whole interval $a\le x\le4a$ above a knot, $h(x)=\frac12x^2+4ax-\frac{16}5a^2$. -/
theorem formula_above_interval (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) (x : ℝ)
    (hlo : a ≤ x) (hhi : x ≤ 4 * a) : objective x = 1 / 2 * x ^ 2 + 4 * a * x - 16 / 5 * a ^ 2 := by
  rw [ha, knot_of_index j hj] at hlo hhi ⊢
  rw [objective_formula_above (j - 1) hlo hhi]
  ring

open AccumulatingKinks in
/-- Item `C/05_G/disp/029` (`companion/chapters/05_G.tex:302-304`): just above a knot $a$,
\[ h(x)=\frac12x^2+4ax-\frac{16}{5}a^2 \]
(for all $x>a$ close to $a$; in fact on $a\le x\le4a$, `formula_above_interval`). -/
theorem formula_above (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    ∀ᶠ x in 𝓝[>] a, objective x = 1 / 2 * x ^ 2 + 4 * a * x - 16 / 5 * a ^ 2 := by
  have hpos : 0 < a := by rw [ha]; positivity
  filter_upwards [Ioo_mem_nhdsGT (show a < 4 * a by linarith)] with x hx
  exact formula_above_interval j hj a ha x hx.1.le hx.2.le

open AccumulatingKinks in
/-- Item `C/05_G/prose/061` (`companion/chapters/05_G.tex:305`): "Also $h(a)=13a^2/10$." -/
theorem h_at_knot (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    objective a = 13 * a ^ 2 / 10 := by
  rw [ha, knot_of_index j hj, objective_knot]
  ring

open AccumulatingKinks OneDimensional in
/-- Item `C/05_G/disp/030` (`companion/chapters/05_G.tex:308-310`): fix a knot $a$ and let
$x=a+\varepsilon$, $z=a-\varepsilon$, $\varepsilon\downarrow0$. Exactly (for small
$\varepsilon>0$), the gradients are
\[ g_x=5a+\varepsilon,\quad g_z=2a-\varepsilon,\quad y=-3a-2\varepsilon. \] -/
theorem knot_crossing_gradients (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      HasFDerivAt coordinateObjective (gradientFunctional (embed (5 * a + ε))) (embed (a + ε)) ∧
      HasFDerivAt coordinateObjective (gradientFunctional (embed (2 * a - ε))) (embed (a - ε)) ∧
      (2 * a - ε) - (5 * a + ε) = -3 * a - 2 * ε := by
  have hpos : 0 < a := by rw [ha]; positivity
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a / 8 by positivity)] with ε hε
  rw [ha, knot_of_index j hj] at hε ⊢
  exact ⟨(crossing_gradients (j - 1) hε.1 hε.2.le).1, (crossing_gradients (j - 1) hε.1 hε.2.le).2,
    by ring⟩

open AccumulatingKinks OneDimensional in
/-- Item `C/05_G/disp/031` (`companion/chapters/05_G.tex:311-315`): for these pairs (small
$\varepsilon>0$),
\[ d=10a\varepsilon+2\varepsilon^2,\qquad\Delta=7a\varepsilon,\qquad
   t=6a\varepsilon+4\varepsilon^2. \] -/
theorem knot_crossing_quantities (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      -dot (embed (5 * a + ε)) (embed (a - ε) - embed (a + ε)) = 10 * a * ε + 2 * ε ^ 2 ∧
      coordinateObjective (embed (a + ε)) - coordinateObjective (embed (a - ε)) = 7 * a * ε ∧
      dot (embed (2 * a - ε) - embed (5 * a + ε)) (embed (a - ε) - embed (a + ε)) =
        6 * a * ε + 4 * ε ^ 2 := by
  have hpos : 0 < a := by rw [ha]; positivity
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a / 8 by positivity)] with ε hε
  rw [ha, knot_of_index j hj] at hε ⊢
  have hv := crossing_values (j - 1) hε.1 hε.2.le
  refine ⟨crossing_decrease (j - 1) ε, ?_, crossing_curvature (j - 1) ε⟩
  change coordinateObjective (crossingX (j - 1) ε) - coordinateObjective (crossingZ (j - 1) ε) = _
  rw [hv.1, hv.2]
  ring

open AccumulatingKinks OneDimensional in
/-- Item `C/05_G/prose/062` (`companion/chapters/05_G.tex:316`): "The pairs are strictly
eligible for $(c_1,c_2)=(1/4,1/2)$ for small $\varepsilon$." -/
theorem knot_crossing_eligible (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      EligiblePair coordinateObjective (1 / 4) (1 / 2) (embed (a + ε)) (embed (a - ε))
          (embed (5 * a + ε)) (embed (2 * a - ε)) ∧
        0 < -dot (embed (5 * a + ε)) (embed (a - ε) - embed (a + ε)) ∧
        1 / 4 * -dot (embed (5 * a + ε)) (embed (a - ε) - embed (a + ε)) <
          coordinateObjective (embed (a + ε)) - coordinateObjective (embed (a - ε)) ∧
        coordinateObjective (embed (a + ε)) - coordinateObjective (embed (a - ε)) <
          -dot (embed (5 * a + ε)) (embed (a - ε) - embed (a + ε)) ∧
        (1 - 1 / 2) * -dot (embed (5 * a + ε)) (embed (a - ε) - embed (a + ε)) <
          dot (embed (2 * a - ε) - embed (5 * a + ε)) (embed (a - ε) - embed (a + ε)) := by
  have hpos : 0 < a := by rw [ha]; positivity
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a / 8 by positivity)] with ε hε
  rw [ha, knot_of_index j hj] at hε ⊢
  exact ⟨crossing_eligible (j - 1) hε.1 hε.2.le, crossing_strict (j - 1) hε.1 hε.2.le⟩

open AccumulatingKinks in
/-- Item `C/05_G/disp/032` (`companion/chapters/05_G.tex:317-320`): yet
\[ \frac{|y|}{|s|\,g_z^2}=\frac{3a+2\varepsilon}{2\varepsilon(2a-\varepsilon)^2}
   \longrightarrow\infty. \] -/
theorem knot_quotient (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    (∀ ε : ℝ, 0 < ε → |(2 * a - ε) - (5 * a + ε)| / (|(a - ε) - (a + ε)| * (2 * a - ε) ^ 2) =
      (3 * a + 2 * ε) / (2 * ε * (2 * a - ε) ^ 2)) ∧
    Tendsto (fun ε => (3 * a + 2 * ε) / (2 * ε * (2 * a - ε) ^ 2)) (𝓝[>] 0) atTop := by
  rw [ha, knot_of_index j hj]
  refine ⟨fun ε hε => crossing_quotient (j - 1) hε, ?_⟩
  refine (crossing_quotient_tendsto (j - 1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact crossing_quotient (j - 1) hε

/-- A polynomial expression vanishing at $0$ tends to $0$ as $\varepsilon\downarrow0$. -/
theorem tendsto_zero_of_continuous {p : ℝ → ℝ} (hp : Continuous p) (h0 : p 0 = 0) :
    Tendsto p (𝓝[>] 0) (𝓝 0) := by
  have := hp.tendsto 0
  rw [h0] at this
  exact this.mono_left nhdsWithin_le_nhds

open AccumulatingKinks OneDimensional in
/-- Item `C/05_G/prose/065` (`companion/chapters/05_G.tex:321`): "Fixing a knot first, then
taking $\epsilon\to0$, is essential: deterioration of band constants as $\eta\downarrow0$ cannot
repair the divergence on the fixed knot's band." For a knot $a=a_j$, every compact sublevel
$K=\{h\le b\}$ with $b>h(a)$ and every $0<\eta<h(a)$ (the knot lies in the interior of the band
$K_\eta$: the fixed knot's band; $F_*=h(0)=0$), there is no band certificate on $K_\eta$ for
$(c_1,c_2)=(1/4,1/2)$, whatever its constants.

Also Item `C/05_G/prose/063` (`companion/chapters/05_G.tex:321`), corrected on 15 October 2026
(M23; before "No certificate exists on a positive band containing this knot."): "No certificate
exists on a positive band whose interior contains this knot ($b>h(a)>\eta$)." Proof: the crossing
pairs $a\pm\varepsilon$ are eligible arbitrarily small crossings of the derivative jump $2a<5a$
(`small_crossing_no_certificate`). -/
theorem no_certificate_knot_band (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j)
    (b : ℝ) (hb : objective a < b) (η : ℝ) (hη : 0 < η) (hηa : η < objective a) :
    ¬ Nonempty (BandCertificate coordinateObjective {x | coordinateObjective x ≤ b} 0
      (1 / 4) (1 / 2) η) := by
  have hpos : 0 < a := by rw [ha]; positivity
  have hknot : a = knot (j - 1) := by rw [ha, knot_of_index j hj]
  have hha : objective a = 13 / 10 * a ^ 2 := by rw [hknot, objective_knot]
  have hFstar : IsLeast (Set.range coordinateObjective) 0 :=
    ⟨⟨0, coordinateObjective_zero⟩, by
      rintro _ ⟨x, rfl⟩
      simpa using coordinateObjective_minimum x⟩
  have hl : HasDerivWithinAt (fun t => coordinateObjective (embed t)) (2 * a) (Iio a) a := by
    rw [hknot]
    exact (hasDerivWithinAt_knot_left (j - 1)).mono Iio_subset_Iic_self
  have hr : HasDerivWithinAt (fun t => coordinateObjective (embed t)) (5 * a) (Ioi a) a := by
    rw [hknot]
    exact (hasDerivWithinAt_knot_right (j - 1)).mono Ioi_subset_Ici_self
  refine small_crossing_no_certificate coordinateObjective_convex 0 hFstar b _ rfl
    (coordinateObjective_sublevel_compact b) (1 / 4) (1 / 2) (by norm_num) η hη _ rfl a
    (2 * a) (5 * a) (by simpa using lt_trans hη hηa) hl hr (by linarith) ?_
  intro ε hε
  have e1 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e ∧ e < a / 8 := Ioo_mem_nhdsGT (by positivity)
  have e2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 10 * a * e + 2 * e ^ 2 < ε :=
    (tendsto_zero_of_continuous (p := fun e => 10 * a * e + 2 * e ^ 2) (by fun_prop)
      (by ring)).eventually (gt_mem_nhds hε)
  have e3 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 2 * e < ε :=
    (tendsto_zero_of_continuous (p := fun e => 2 * e) (by fun_prop) (by ring)).eventually
      (gt_mem_nhds hε)
  have e4 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 5 * a * e + e ^ 2 / 2 < b - objective a :=
    (tendsto_zero_of_continuous (p := fun e => 5 * a * e + e ^ 2 / 2) (by fun_prop)
      (by ring)).eventually (gt_mem_nhds (by linarith))
  have e5 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 2 * a * e < objective a - η :=
    (tendsto_zero_of_continuous (p := fun e => 2 * a * e) (by fun_prop) (by ring)).eventually
      (gt_mem_nhds (by linarith))
  obtain ⟨e, ⟨he, hea⟩, h2, h3, h4, h5⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  have hs : e ≤ knot (j - 1) / 8 := by rw [← hknot]; exact hea.le
  have hv := crossing_values (j - 1) he hs
  rw [← hknot] at hv
  refine ⟨crossingX (j - 1) e, crossingZ (j - 1) e, crossingG (j - 1) e, crossingH (j - 1) e,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, crossing_eligible (j - 1) he hs, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · show coordinateObjective (crossingX (j - 1) e) ≤ b
    rw [hv.1]; nlinarith
  · show coordinateObjective (crossingX (j - 1) e) ≥ 0 + η
    rw [hv.1]; nlinarith [sq_nonneg e]
  · show coordinateObjective (crossingZ (j - 1) e) ≤ b
    rw [hv.2]; nlinarith
  · show coordinateObjective (crossingZ (j - 1) e) ≥ 0 + η
    rw [hv.2]; nlinarith [sq_nonneg e]
  · have := crossing_decrease (j - 1) e
    rw [← hknot] at this
    change pairDecrease _ _ _ ≤ ε
    rw [this]; linarith
  · simp only [crossingX, crossingZ, embed_apply]
    rw [← hknot, show a - e - (a + e) = -(2 * e) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  · simp only [crossingZ, embed_apply]; linarith
  · simp only [crossingX, embed_apply]; rw [← hknot]; linarith

open AccumulatingKinks in
/-- $h$ is strictly increasing on $[0,\infty)$. -/
theorem objective_strictMonoOn : StrictMonoOn objective (Ici 0) := by
  intro s hs t ht hst
  have hmono : kinkSum s ≤ kinkSum t :=
    (term_summable s).tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left
      (max_le_max (by linarith) le_rfl) (knot_pos j).le) (term_summable t)
  have hs0 : (0 : ℝ) ≤ s := hs
  unfold objective
  nlinarith

open AccumulatingKinks in
/-- The differentiable points of the band $K_\eta$, $K=\{h\le h(a)\}$, $\eta=h(a/4)$, at a knot
$a$: either $a/4<x<a$ with $h'(x)=x+a$, or $x<0$ with $h'(x)=x$ and $x^2\ge2\eta$. -/
theorem edge_band_points (i : ℕ) {x g : Vec 1}
    (hx : x ∈ positiveBand coordinateObjective {x | coordinateObjective x ≤ objective (knot i)} 0
      (objective (knot i / 4)))
    (hg : HasFDerivAt coordinateObjective (gradientFunctional g) x) :
    (knot i / 4 < x 0 ∧ x 0 < knot i ∧ g 0 = x 0 + knot i) ∨
      (x 0 < 0 ∧ g 0 = x 0 ∧ 2 * objective (knot i / 4) ≤ x 0 ^ 2) := by
  have hd : HasDerivAt objective (g 0) (x 0) := scalar_derivative hg
  have hk := knot_pos i
  have hup : objective (x 0) ≤ objective (knot i) := hx.1
  have hlo : 0 + objective (knot i / 4) ≤ objective (x 0) := hx.2
  have hq : 0 < objective (knot i / 4) := by
    rw [← knot_succ, objective_knot]; have := knot_pos (i + 1); positivity
  rcases lt_trichotomy (x 0) 0 with hneg | hzero | hpos
  · right
    have hd' : HasDerivAt objective (x 0) (x 0) := by
      apply (BfgsCoverage.Article.Energy.Example.quad_hasDerivAt (x 0)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hneg] with t ht
      exact objective_nonpos ht.le
    have hgx : g 0 = x 0 := hd.unique hd'
    rw [objective_nonpos hneg.le] at hlo
    exact ⟨hneg, hgx, by linarith⟩
  · rw [hzero, objective_zero] at hlo
    linarith
  · left
    have hle : x 0 ≤ knot i := by
      by_contra h
      have := objective_strictMonoOn (le_of_lt hk : (0 : ℝ) ≤ knot i) hpos.le (lt_of_not_le h)
      linarith
    have hge : knot i / 4 ≤ x 0 := by
      by_contra h
      have := objective_strictMonoOn hpos.le (by positivity : (0 : ℝ) ≤ knot i / 4)
        (lt_of_not_le h)
      linarith
    have hne1 : x 0 ≠ knot i := fun h => not_differentiableAt_knot i (h ▸ hd.differentiableAt)
    have hne2 : x 0 ≠ knot i / 4 := fun h => by
      rw [← knot_succ] at h
      exact not_differentiableAt_knot (i + 1) (h ▸ hd.differentiableAt)
    have hlt1 : x 0 < knot i := lt_of_le_of_ne hle hne1
    have hlt2 : knot i / 4 < x 0 := lt_of_le_of_ne hge (Ne.symm hne2)
    exact ⟨hlt2, hlt1, hd.unique (hasDerivAt_below i hlt2 hlt1)⟩

open AccumulatingKinks in
/-- A band certificate on the band $K_\eta$ of $K=\{h\le h(a)\}$ with $\eta=h(a/4)$, which
contains the knot $a$ (on its boundary): $W=I$, $m=2h(a/4)=13a^2/80$, $C=1$, $L=0$,
$\delta=a^2/8$. No eligible pair with $d\le\delta$ joins the two pieces of the band. -/
def edgeCert (i : ℕ) (c₁ c₂ : ℝ) :
    BandCertificate coordinateObjective {x | coordinateObjective x ≤ objective (knot i)} 0 c₁ c₂
      (objective (knot i / 4)) where
  W := fun _ => 1
  m := 2 * objective (knot i / 4)
  C := 1
  L := 0
  δ := knot i ^ 2 / 8
  m_pos := by
    rw [← knot_succ, objective_knot]; have := knot_pos (i + 1); positivity
  L_nonneg := le_rfl
  delta_pos := by have := knot_pos i; positivity
  positive_semidefinite := fun _ _ _ => Matrix.PosSemidef.one
  visibility := fun x hx g hg => by
    rw [scalar_energy]
    simp only [Matrix.one_apply_eq, one_mul]
    have hq : objective (knot i / 4) = 13 / 160 * knot i ^ 2 := by
      rw [← knot_succ, objective_knot, knot_succ]; ring
    rcases edge_band_points i hx hg with ⟨h1, _, h3⟩ | ⟨_, h2, h3⟩
    · rw [h3, hq]
      have := knot_pos i
      nlinarith
    · rw [h2]; exact h3
  secant := fun x z g h hx hz hp hd => by
    have hk := knot_pos i
    have hdec := hp.decrease_pos
    simp only [pairDecrease, pairStep, dot, Fin.sum_univ_one, Pi.sub_apply] at hd hdec
    rw [scalar_energy]
    simp only [Matrix.one_apply_eq, one_mul, pairCurvature, pairStep, dot, Fin.sum_univ_one,
      Pi.sub_apply]
    have hq : objective (knot i / 4) = 13 / 160 * knot i ^ 2 := by
      rw [← knot_succ, objective_knot, knot_succ]; ring
    rcases edge_band_points i hx hp.gradient_x with ⟨hx1, hx2, hgx⟩ | ⟨hx1, hgx, hx3⟩ <;>
      rcases edge_band_points i hz hp.gradient_z with ⟨hz1, hz2, hhz⟩ | ⟨hz1, hhz, hz3⟩
    · rw [hgx, hhz]; nlinarith
    · rw [hgx] at hd; nlinarith
    · rw [hgx] at hd; rw [hq] at hx3; nlinarith
    · rw [hgx, hhz]; nlinarith
  transport := fun x z g h _ _ hp _ => by
    have hs : pairStep x z ≠ 0 := by
      intro h0
      have := hp.decrease_pos
      simp [pairDecrease, h0, dot] at this
    rw [BfgsCoverage.Article.Energy.stepProjector_one_dim hs]
    simpa using Matrix.PosSemidef.zero

open AccumulatingKinks in
/-- Counterexample to the literal reading of item `C/05_G/prose/063` (line 321) as printed before
its correction of 15 October 2026 (M23; "No certificate exists on a positive band containing this
knot"): for every knot $a=a_j$ the band $K_\eta$ with
$K=\{h\le h(a)\}$ and $\eta=h(a/4)>0$ contains the knot $a$, yet it carries a band certificate
(`edgeCert`) for $(c_1,c_2)=(1/4,1/2)$. The knot lies on the boundary of this band; the corrected
statement (`no_certificate_knot_band`) requires $b>h(a)>\eta$. -/
theorem knot_band_literal_counterexample (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : a = (1 / 4 : ℝ) ^ j) :
    OneDimensional.embed a ∈ {x | x ∈ {x | coordinateObjective x ≤ objective a} ∧
      coordinateObjective x ≥ 0 + objective (a / 4)} ∧
    0 < objective (a / 4) ∧ IsCompact {x | coordinateObjective x ≤ objective a} ∧
    Nonempty (BandCertificate coordinateObjective {x | coordinateObjective x ≤ objective a} 0
      (1 / 4) (1 / 2) (objective (a / 4))) := by
  rw [ha, knot_of_index j hj]
  set i := j - 1
  have hk := knot_pos i
  have hq : objective (knot i / 4) = 13 / 160 * knot i ^ 2 := by
    rw [← knot_succ, objective_knot, knot_succ]; ring
  refine ⟨⟨show objective (knot i) ≤ objective (knot i) from le_refl _, ?_⟩, by rw [hq]; positivity,
    coordinateObjective_sublevel_compact _,
    ⟨edgeCert i (1 / 4) (1 / 2)⟩⟩
  show 0 + objective (knot i / 4) ≤ objective (knot i)
  rw [hq, objective_knot]
  nlinarith

/-- Item `C/05_G/prose/064` (`companion/chapters/05_G.tex:321`): "Every neighborhood of zero
contains such a knot." -/
theorem every_neighborhood_knot (U : Set ℝ) (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ j : ℕ, 1 ≤ j ∧ (1 / 4 : ℝ) ^ j ∈ U := by
  obtain ⟨i, hi⟩ := (AccumulatingKinks.knot_tendsto.eventually hU).exists
  exact ⟨i + 1, by omega, by simpa [AccumulatingKinks.knot] using hi⟩

open AccumulatingKinks OneDimensional in
/-- Item `C/05_G/prose/066` (`companion/chapters/05_G.tex:323`): "Nevertheless Proposition
`G:prop:scalarconv` proves convergence of every admissible run on $h$." Every admissible run on
$h$ (on $\R^1$), and every positive-metric scalar run, converges to the minimizer $0$ (values and
iterates); such runs exist (`kinkRun`). -/
theorem h_runs_converge :
    (∀ R : AdmissibleBFGSRun 1 coordinateObjective,
      Tendsto (fun k => coordinateObjective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
    (∀ R : ScalarMetricRun objective,
      Tendsto (fun k => objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) :=
  ⟨actual_bfgs_converges, scalar_run_converges⟩

open AccumulatingKinks in
/-- Item `C/05_G/prose/067` (`companion/chapters/05_G.tex:323`): "The minimizer is
differentiable for this scalar example, but the objective is nonsmooth in every neighborhood of
it." $h'(0)=0$, and every neighborhood of $0$ contains a point where $h$ is not
differentiable (a knot). -/
theorem h_smoothness :
    HasDerivAt objective 0 0 ∧ ∀ U ∈ 𝓝 (0 : ℝ), ∃ x ∈ U, ¬ DifferentiableAt ℝ objective x :=
  ⟨hasDerivAt_zero, fun _ hU => nonsmooth_in_every_neighborhood hU⟩

open AccumulatingKinks in
/-- Item `C/05_G/prose/068` (`companion/chapters/05_G.tex:323`): "Thus the transported
condition is not necessary even for local convergence." For $h$ and $(c_1,c_2)=(1/4,1/2)$: no
neighborhood $K$ of the minimizer carries the band certificates, yet every admissible run
converges to the minimizer. -/
theorem local_nonnecessity :
    (∀ K : Set (Vec 1), K ∈ 𝓝 (0 : Vec 1) →
      ¬ HasBandCertificates coordinateObjective K 0 (1 / 4) (1 / 2)) ∧
    ∀ R : AdmissibleBFGSRun 1 coordinateObjective,
      Tendsto (fun k => coordinateObjective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) :=
  ⟨fun _ hK => every_neighborhood_no_certificates hK, actual_bfgs_converges⟩

open ScalarCounterexamples OneDimensional in
/-- Item `C/05_G/prose/002` (`companion/chapters/05_G.tex:3`): "Its normalization and
pointwise geometry help interpret it, while scalar examples separate failure of the condition
from failure of BFGS." Two scalar examples where the condition fails and BFGS does not:
$f(x)=\frac12(x+2)^2+|x|$ has no band certificates on $\{f\le3\}$ for $(1/4,1/2)$, and the
accumulating-kink objective $h$ has none on any neighborhood of its minimizer; yet every
admissible run converges on both. -/
theorem scalar_examples_separate :
    (¬ HasBandCertificates shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) ∧
      ∀ R : AdmissibleBFGSRun 1 shiftedObjective,
        Tendsto (fun k => shiftedObjective (R.x k)) atTop (𝓝 (3 / 2)) ∧
          Tendsto R.x atTop (𝓝 (embed (-1)))) ∧
    (∀ K : Set (Vec 1), K ∈ 𝓝 (0 : Vec 1) →
        ¬ HasBandCertificates AccumulatingKinks.coordinateObjective K 0 (1 / 4) (1 / 2)) ∧
      ∀ R : AdmissibleBFGSRun 1 AccumulatingKinks.coordinateObjective,
        Tendsto (fun k => AccumulatingKinks.coordinateObjective (R.x k)) atTop (𝓝 0) ∧
          Tendsto R.x atTop (𝓝 0) :=
  ⟨⟨shifted_no_band_certificates, shifted_actual_bfgs_converges⟩, local_nonnecessity⟩

/-! ### Section 5.9: why numerical nonexistence is intrinsically delicate (lines 332-349) -/

/-- Item `C/05_G/proposition/004` (`companion/chapters/05_G.tex:334-336`), Proposition 5.9.1 (Every
finite sample is feasible if constants are free): for finitely many differentiable nonstationary
endpoints $x_i$ (gradients $g_i\ne0$) and finitely many eligible pairs between them, there are
finite constants $m>0$, $C\ge0$ such that the constant field $W\equiv I$ satisfies (V), (S) and
(T0) on the sample. -/
theorem finite_sample_feasible {n r : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (x g : Fin r → Vec n)
    (_hdiff : ∀ i, HasFDerivAt F (gradientFunctional (g i)) (x i)) (hg : ∀ i, g i ≠ 0)
    (P : Finset (Fin r × Fin r))
    (hP : ∀ p ∈ P, EligiblePair F c₁ c₂ (x p.1) (x p.2) (g p.1) (g p.2)) :
    ∃ m C : ℝ, 0 < m ∧ 0 ≤ C ∧
      (∀ i, dot (g i) ((1 : Mat n) *ᵥ g i) ≥ m) ∧
      (∀ p ∈ P, dot (g p.2 - g p.1) ((1 : Mat n) *ᵥ (g p.2 - g p.1)) ≤
        C * dot (g p.2 - g p.1) (x p.2 - x p.1)) ∧
      (∀ p ∈ P, (stepProjector (x p.2 - x p.1) * (1 : Mat n) * stepProjector (x p.2 - x p.1) -
          stepProjector (x p.2 - x p.1) * (1 : Mat n) * stepProjector (x p.2 - x p.1)).PosSemidef) := by
  obtain ⟨m, C, _h1, hm, hC, hV, hS, _hT⟩ := finite_sample_identity_certificate hc.2.2 x g hg P hP
  exact ⟨m, C, hm, hC, hV, hS, fun p _ => by rw [sub_self]; exact Matrix.PosSemidef.zero⟩

/-- Item `C/05_G/disp/033` (`companion/chapters/05_G.tex:339-342`), in the proof of the
Proposition (Every finite sample is feasible): with the finite pair sample $\mathcal P$,
\[ C=\sum_{(x,z)\in\mathcal P}\frac{\|\nabla F(z)-\nabla F(x)\|^2}{t(x,z)}. \]
Next sentences: all denominators are positive, every summand is nonnegative, the sum is zero
for an empty sample, and $C$ bounds each sampled quotient. -/
theorem sample_constant {n r : ℕ} {F : Vec n → ℝ} (_hF : ConvexOn ℝ univ F) (c₁ c₂ : ℝ)
    (hc : 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) (x g : Fin r → Vec n)
    (_hdiff : ∀ i, HasFDerivAt F (gradientFunctional (g i)) (x i)) (_hg : ∀ i, g i ≠ 0)
    (P : Finset (Fin r × Fin r))
    (hP : ∀ p ∈ P, EligiblePair F c₁ c₂ (x p.1) (x p.2) (g p.1) (g p.2)) (C : ℝ)
    (hC : C = ∑ p ∈ P, sqNorm (g p.2 - g p.1) / dot (g p.2 - g p.1) (x p.2 - x p.1)) :
    (∀ p ∈ P, 0 < dot (g p.2 - g p.1) (x p.2 - x p.1)) ∧
      (∀ p ∈ P, 0 ≤ sqNorm (g p.2 - g p.1) / dot (g p.2 - g p.1) (x p.2 - x p.1)) ∧
      (P = ∅ → C = 0) ∧ 0 ≤ C ∧
      ∀ p ∈ P, sqNorm (g p.2 - g p.1) / dot (g p.2 - g p.1) (x p.2 - x p.1) ≤ C := by
  have ht : ∀ p ∈ P, 0 < dot (g p.2 - g p.1) (x p.2 - x p.1) :=
    fun p hp => eligible_curvature_pos (hP p hp) hc.2.2
  set q : Fin r × Fin r → ℝ :=
    fun p => sqNorm (g p.2 - g p.1) / dot (g p.2 - g p.1) (x p.2 - x p.1) with hq
  have ha : ∀ p ∈ P, 0 ≤ q p := fun p hp => div_nonneg (sqNorm_nonneg _) (ht p hp).le
  refine ⟨ht, ha, fun h0 => by rw [hC, h0, Finset.sum_empty], ?_, fun p hp => ?_⟩
  · rw [hC]; exact Finset.sum_nonneg ha
  · rw [hC]
    exact Finset.single_le_sum ha hp

open ScalarCounterexamples OneDimensional in
/-- Item `C/05_G/prose/073` (`companion/chapters/05_G.tex:345`): "Conversely, passing many
finite tests is not an existence theorem for a uniform field on the continuum." For
$f(x)=\frac12(x+2)^2+|x|$, $(c_1,c_2)=(1/4,1/2)$ and the band $K_{1/4}$ of $K=\{f\le3\}$: every
finite sample of differentiable band points and eligible pairs passes the test with $W\equiv I$
(constants depending on the sample), yet no band certificate exists on this band. -/
theorem finite_tests_not_existence :
    (∀ (r : ℕ) (x g : Fin r → Vec 1),
      (∀ i, x i ∈ positiveBand shiftedObjective {x | shiftedObjective x ≤ 3}
        (shiftedObjective (embed (-1))) (1 / 4)) →
      (∀ i, HasFDerivAt shiftedObjective (gradientFunctional (g i)) (x i)) →
      ∀ P : Finset (Fin r × Fin r),
        (∀ p ∈ P, EligiblePair shiftedObjective (1 / 4) (1 / 2) (x p.1) (x p.2) (g p.1) (g p.2)) →
        ∃ m C : ℝ, 0 < m ∧ 0 ≤ C ∧ (∀ i, dot (g i) ((1 : Mat 1) *ᵥ g i) ≥ m) ∧
          (∀ p ∈ P, dot (g p.2 - g p.1) ((1 : Mat 1) *ᵥ (g p.2 - g p.1)) ≤
            C * dot (g p.2 - g p.1) (x p.2 - x p.1))) ∧
    ¬ Nonempty (BandCertificate shiftedObjective {x | shiftedObjective x ≤ 3}
      (shiftedObjective (embed (-1))) (1 / 4) (1 / 2) (1 / 4)) := by
  refine ⟨fun r x g hx hdiff P hP => ?_, shifted_no_band_certificate⟩
  have hg : ∀ i, g i ≠ 0 := fun i =>
    positive_band_gradient_ne_zero shiftedObjective_convex (embed (-1)) (hdiff i)
      (by linarith [(hx i).2])
  obtain ⟨m, C, hm, hC, hV, hS, _⟩ := finite_sample_feasible shiftedObjective_convex (1 / 4) (1 / 2)
    (by norm_num) x g hdiff hg P hP
  exact ⟨m, C, hm, hC, hV, hS⟩

/-! ### Explicit runs and non-vacuity -/

/-- An admissible run on the accumulating-kink objective $h$ (non-vacuity): $x_k=-2^{-k}$,
$H_k=1$, $\alpha_k=1/2$, $(c_1,c_2)=(1/4,1/2)$; on $x\le0$, $h(x)=x^2/2$. -/
def kinkRun : AdmissibleBFGSRun 1 AccumulatingKinks.coordinateObjective :=
  BfgsCoverage.Article.Global.oneDimRun AccumulatingKinks.coordinateObjective
    AccumulatingKinks.coordinateObjective_convex (fun k => -(1 / 2) ^ k) (fun k => -(1 / 2) ^ k)
    (fun _ => 1) (fun _ => 1 / 2) (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) one_pos
    (fun _ => by norm_num) (fun k => neg_ne_zero.mpr (pow_ne_zero k (by norm_num)))
    (fun k => by
      have hneg : -(1 / 2 : ℝ) ^ k < 0 := by
        have : (0 : ℝ) < (1 / 2) ^ k := by positivity
        linarith
      have hd : HasDerivAt AccumulatingKinks.objective (-(1 / 2) ^ k) (-(1 / 2) ^ k) := by
        apply (BfgsCoverage.Article.Energy.Example.quad_hasDerivAt (-(1 / 2) ^ k)).congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hneg] with t ht
        exact AccumulatingKinks.objective_nonpos ht.le
      exact ScalarCounterexamples.coordinate_hasGradient hd)
    (fun k => by
      dsimp only
      rw [pow_succ (1 / 2 : ℝ) k]
      ring)
    (fun k => by
      dsimp only
      have : (0 : ℝ) < (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      have : (0 : ℝ) < (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      rw [div_self]
      have : (0 : ℝ) < (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      have hp : (0 : ℝ) < (1 / 2) ^ k := by positivity
      have h1 : -(1 / 2 : ℝ) ^ (k + 1) ≤ 0 := by
        have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
        linarith
      have h0 : -(1 / 2 : ℝ) ^ k ≤ 0 := by linarith
      change AccumulatingKinks.objective (-(1 / 2) ^ (k + 1)) ≤
        AccumulatingKinks.objective (-(1 / 2) ^ k) + _
      rw [AccumulatingKinks.objective_nonpos h1, AccumulatingKinks.objective_nonpos h0,
        pow_succ (1 / 2 : ℝ) k]
      nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ k)])
    (fun k => by
      dsimp only
      rw [pow_succ (1 / 2 : ℝ) k]
      nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ k)])

/-- A scaled admissible run on $F(x)=x^2/2$ (non-vacuity of the local theorem): $x_k=c2^{-k}$,
$H_k=1$, $\alpha_k=1/2$, $(c_1,c_2)=(1/4,1/2)$. -/
def quadRun (c : ℝ) (hc : 0 < c) : AdmissibleBFGSRun 1 BfgsCoverage.Article.Energy.Example.quad :=
  BfgsCoverage.Article.Global.oneDimRun BfgsCoverage.Article.Energy.Example.quad
    BfgsCoverage.Article.Energy.Example.quad_convex (fun k => c * (1 / 2) ^ k)
    (fun k => c * (1 / 2) ^ k) (fun _ => 1) (fun _ => 1 / 2) (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) one_pos (fun _ => by norm_num)
    (fun k => mul_ne_zero hc.ne' (pow_ne_zero k (by norm_num)))
    (fun k => BfgsCoverage.Article.Energy.Example.quad_hasGradient _)
    (fun k => by
      dsimp only
      rw [pow_succ (1 / 2 : ℝ) k]
      ring)
    (fun k => by
      dsimp only
      have : (0 : ℝ) < c * (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      have : (0 : ℝ) < c * (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      rw [div_self]
      have : (0 : ℝ) < c * (1 / 2) ^ k := by positivity
      rw [pow_succ (1 / 2 : ℝ) k]
      intro h
      nlinarith)
    (fun k => by
      dsimp only
      simp only [BfgsCoverage.Article.Energy.Example.quad, OneDimensional.embed_apply]
      rw [pow_succ (1 / 2 : ℝ) k]
      nlinarith [sq_nonneg (c * (1 / 2 : ℝ) ^ k)])
    (fun k => by
      dsimp only
      rw [pow_succ (1 / 2 : ℝ) k]
      nlinarith [sq_nonneg (c * (1 / 2 : ℝ) ^ k)])

/-- The standing assumptions of Section 5.1, together with the condition (5.V)--(5.T) on a
nonempty band (so also the hypotheses of `condition_iff`, `exact_nonexpansion_normalization`,
`pointwise_characterization`, `proof_direction` with $C>0$, `exact_scalar_characterization`),
can all hold at once: $F(x)=x^2/2$ on $\R^1$, $F_*=0$, $K=\{F\le1\}$, $(c_1,c_2)=(1/4,1/2)$,
$\eta=1/8$, with the certificate $W=I$. -/
example : ∃ (F : Vec 1 → ℝ) (Fstar b : ℝ) (K : Set (Vec 1)) (c₁ c₂ η : ℝ),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ K = {x | F x ≤ b} ∧ IsCompact K ∧
      (0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) ∧ 0 < η ∧ {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty ∧
      Nonempty (BandCertificate F K Fstar c₁ c₂ η) ∧
      ∃ B : VisibilitySecantCertificate F K Fstar c₁ c₂ η, 0 < B.C := by
  refine ⟨BfgsCoverage.Article.Energy.Example.quad, 0, 1, _, 1 / 4, 1 / 2, 1 / 8,
    BfgsCoverage.Article.Energy.Example.quad_convex,
    BfgsCoverage.Article.Energy.Example.quad_isLeast, rfl,
    BfgsCoverage.Article.Energy.Example.quad_sublevel_compact 1, by norm_num, by norm_num,
    ⟨fun _ => 1, ?_⟩, ⟨BfgsCoverage.Article.Energy.Example.quadCert _ _ _ _ (by norm_num)⟩,
    ⟨(BfgsCoverage.Article.Energy.Example.quadCert _ _ _ _ (by norm_num)).toVisibilitySecant,
      one_pos⟩⟩
  constructor <;> norm_num [BfgsCoverage.Article.Energy.Example.quad]

/-- The hypotheses of `preceding_theorem` can hold with an admissible run: $F(x)=x^2/2$,
$K=\{F\le1\}$, the run $x_k=2^{-k}$ of the energy coverage module, certificates $W=I$. -/
example : ∃ (F : Vec 1 → ℝ) (Fstar b : ℝ) (K : Set (Vec 1)) (R : AdmissibleBFGSRun 1 F),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ K = {x | F x ≤ b} ∧ IsCompact K ∧
      (0 < R.c₁ ∧ R.c₁ < R.c₂ ∧ R.c₂ < 1) ∧
      (∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
        Nonempty (BandCertificate F K Fstar R.c₁ R.c₂ η)) ∧ R.x 0 ∈ K := by
  refine ⟨BfgsCoverage.Article.Energy.Example.quad, 0, 1, _, BfgsCoverage.Article.Energy.Example.run,
    BfgsCoverage.Article.Energy.Example.quad_convex,
    BfgsCoverage.Article.Energy.Example.quad_isLeast, rfl,
    BfgsCoverage.Article.Energy.Example.quad_sublevel_compact 1,
    ⟨BfgsCoverage.Article.Energy.Example.run.c₁_pos, BfgsCoverage.Article.Energy.Example.run.c₁_lt_c₂,
      BfgsCoverage.Article.Energy.Example.run.c₂_lt_one⟩,
    fun η hη _ => ⟨BfgsCoverage.Article.Energy.Example.quadCert _ _ _ η hη⟩, ?_⟩
  show BfgsCoverage.Article.Energy.Example.quad (BfgsCoverage.Article.Energy.Example.pt 0) ≤ 1
  norm_num [BfgsCoverage.Article.Energy.Example.quad, BfgsCoverage.Article.Energy.Example.pt]

/-- The hypotheses of `local_theorem` can hold, and for every $\delta>0$ some admissible run
with the given constants starts below $F_*+\delta$ (so its conclusion is not vacuous):
$F(x)=x^2/2$, $x_*=0$, $b=1$, $U=\R^1$, $(c_1,c_2)=(1/4,1/2)$, runs `quadRun`. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (b : ℝ) (U : Set (Vec 1)) (c₁ c₂ : ℝ),
    ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      F xstar < b ∧ IsCompact {x | F x ≤ b} ∧ U ∈ 𝓝 xstar ∧
      (∀ η : ℝ, 0 < η → {x | x ∈ {x | F x ≤ b} ∩ U ∧ F x ≥ F xstar + η}.Nonempty →
        Nonempty (BandCertificate F ({x | F x ≤ b} ∩ U) (F xstar) c₁ c₂ η)) ∧
      ∀ δ : ℝ, 0 < δ → ∃ R : AdmissibleBFGSRun 1 F, R.c₁ = c₁ ∧ R.c₂ = c₂ ∧
        F (R.x 0) ≤ F xstar + δ := by
  have hq0 : BfgsCoverage.Article.Energy.Example.quad 0 = 0 := by
    simp [BfgsCoverage.Article.Energy.Example.quad]
  refine ⟨BfgsCoverage.Article.Energy.Example.quad, 0, 1, univ, 1 / 4, 1 / 2,
    BfgsCoverage.Article.Energy.Example.quad_convex,
    fun x => by rw [hq0]; exact BfgsCoverage.Article.Energy.Example.quad_nonneg x, ?_,
    by rw [hq0]; norm_num, BfgsCoverage.Article.Energy.Example.quad_sublevel_compact 1,
    univ_mem, fun η hη _ => ⟨?_⟩, fun δ hδ => ?_⟩
  · intro x hx
    rw [hq0] at hx
    funext i
    fin_cases i
    simp only [BfgsCoverage.Article.Energy.Example.quad] at hx
    simpa using hx
  · rw [hq0]
    exact BfgsCoverage.Article.Energy.Example.quadCert _ _ _ η hη
  · refine ⟨quadRun (min 1 δ) (lt_min one_pos hδ), rfl, rfl, ?_⟩
    have h1 : min 1 δ ≤ 1 := min_le_left _ _
    have h2 : min 1 δ ≤ δ := min_le_right _ _
    have h3 : 0 < min 1 δ := lt_min one_pos hδ
    rw [hq0]
    show (min 1 δ * (1 / 2) ^ 0) ^ 2 / 2 ≤ 0 + δ
    nlinarith

/-- Admissible runs exist on $f(x)=\frac12(x+2)^2+|x|$ and on the accumulating-kink objective
$h$, with $(c_1,c_2)=(1/4,1/2)$: the convergence statements `shifted_global_nonnecessity`,
`h_runs_converge` and `local_nonnecessity` about every admissible run are not vacuous. -/
example : shiftedRun.c₁ = 1 / 4 ∧ shiftedRun.c₂ = 1 / 2 ∧ kinkRun.c₁ = 1 / 4 ∧
    kinkRun.c₂ = 1 / 2 := ⟨rfl, rfl, rfl, rfl⟩

/-- The hypotheses of `scalar_convergence` (Proposition `G:prop:scalarconv`) can all hold: the
scalar data of `kinkRun` on $h$ (minimizer $0$). -/
example : ∃ (f : ℝ → ℝ) (xstar : ℝ) (x g M α : ℕ → ℝ) (c₁ c₂ : ℝ),
    ConvexOn ℝ univ f ∧ (∀ y, f xstar ≤ f y) ∧ (∀ y, f y = f xstar → y = xstar) ∧
      0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧ (∀ k, 0 < M k) ∧ (∀ k, 0 < α k) ∧ (∀ k, g k ≠ 0) ∧
      (∀ k, HasDerivAt f (g k) (x k)) ∧ (∀ k, x (k + 1) = x k - α k * M k * g k) ∧
      (∀ k, f (x (k + 1)) ≤ f (x k) + c₁ * g k * (x (k + 1) - x k)) ∧
      (∀ k, g (k + 1) * (x (k + 1) - x k) ≥ c₂ * g k * (x (k + 1) - x k)) ∧
      IsCompact {y | f y ≤ f (x 0)} := by
  let R := kinkRun.toScalarMetricRun
  refine ⟨OneDimensional.objective AccumulatingKinks.coordinateObjective, 0, R.x, R.g, R.metric,
    R.α, R.c₁, R.c₂, R.convex, fun y => AccumulatingKinks.objective_minimum y,
    fun y hy => AccumulatingKinks.objective_unique y hy, R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one,
    R.metric_pos, R.alpha_pos, R.gradient_ne, R.hasDeriv, R.step, R.armijo, R.weak_wolfe,
    AccumulatingKinks.objective_sublevel_compact _⟩

open ScalarCounterexamples OneDimensional in
/-- The hypotheses of Proposition `G:prop:star` (`incoming_jump_obstruction`) can all hold, for
an actual objective: $f(x)=\frac12(x+2)^2+|x|$, $(c_1,c_2)=(1/4,1/2)$, the band $K_{1/4}$ of
$K=\{f\le3\}$, one predecessor ($r=1$): $z_k=-\varepsilon_k/2$, $x_k=\varepsilon_k$ with
$\varepsilon_k\to0$, $\lambda_k=\nabla f(z_k)/y_k$. -/
example : ∃ (z h : ℕ → Vec 1) (x g y : ℕ → Fin 1 → Vec 1) (t lam : ℕ → Fin 1 → ℝ),
    (∀ k, z k ∈ {x | x ∈ {x | shiftedObjective x ≤ 3} ∧
      shiftedObjective x ≥ shiftedObjective (embed (-1)) + 1 / 4}) ∧
    (∀ k j, x k j ∈ {x | x ∈ {x | shiftedObjective x ≤ 3} ∧
      shiftedObjective x ≥ shiftedObjective (embed (-1)) + 1 / 4}) ∧
    (∀ k, HasFDerivAt shiftedObjective (gradientFunctional (h k)) (z k)) ∧
    (∀ k j, EligiblePair shiftedObjective (1 / 4) (1 / 2) (x k j) (z k) (g k j) (h k)) ∧
    (∀ j, Tendsto (fun k => -dot (g k j) (z k - x k j)) atTop (𝓝 0)) ∧
    (∀ k j, y k j = h k - g k j) ∧ (∀ k j, t k j = dot (y k j) (z k - x k j)) ∧
    (∀ k, h k = ∑ j, lam k j • y k j) ∧
    Tendsto (fun k => ∑ j, |lam k j| * Real.sqrt (t k j)) atTop (𝓝 0) := by
  let ε : ℕ → ℝ := crossingScale
  have hε : ∀ k, 0 < ε k := crossingScale_pos
  have hε8 : ∀ k, ε k ≤ 1 / 8 := crossingScale_le
  have hden : ∀ k, (-2 - 3 / 2 * ε k : ℝ) ≠ 0 := fun k => by linarith [hε k]
  refine ⟨fun k => crossingZ (ε k), fun k => crossingH (ε k), fun k _ => crossingX (ε k),
    fun k _ => crossingG (ε k), fun k _ => crossingH (ε k) - crossingG (ε k),
    fun k _ => dot (crossingH (ε k) - crossingG (ε k)) (crossingZ (ε k) - crossingX (ε k)),
    fun k _ => (1 - ε k / 2) / (-2 - 3 / 2 * ε k),
    fun k => (crossing_band (hε k) (hε8 k)).2, fun k _ => (crossing_band (hε k) (hε8 k)).1,
    fun k => (crossing_gradients (hε k)).2, fun k _ => crossing_eligible (hε k),
    fun _ => crossing_decrease_tendsto, fun _ _ => rfl, fun _ _ => rfl, fun k => ?_, ?_⟩
  · simp only [Fin.sum_univ_one]
    ext i
    fin_cases i
    simp only [crossingH, crossingG, Pi.smul_apply, Pi.sub_apply, embed_apply, smul_eq_mul]
    have he : 1 - ε k / 2 - (3 + ε k) = -2 - 3 / 2 * ε k := by ring
    rw [he, div_mul_cancel₀ _ (hden k)]
  · simp only [Fin.sum_univ_one]
    have ht : ∀ k, dot (crossingH (ε k) - crossingG (ε k)) (crossingZ (ε k) - crossingX (ε k)) =
        3 * ε k + 9 / 4 * ε k ^ 2 := fun k => crossing_curvature (ε k)
    simp only [ht]
    have hlim : Tendsto (fun k => Real.sqrt (3 * ε k + 9 / 4 * ε k ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => 3 * ε k + 9 / 4 * ε k ^ 2) atTop (𝓝 0) := by
        simpa using (crossingScale_tendsto.const_mul 3).add
          ((crossingScale_tendsto.pow 2).const_mul (9 / 4 : ℝ))
      simpa using h1.sqrt
    refine squeeze_zero (fun k => by positivity) (fun k => ?_) hlim
    have hl : |(1 - ε k / 2) / (-2 - 3 / 2 * ε k)| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr (hden k))]
      rw [abs_of_pos (by linarith [hε8 k]), abs_of_neg (by linarith [hε k])]
      linarith [hε k]
    calc |(1 - ε k / 2) / (-2 - 3 / 2 * ε k)| * Real.sqrt (3 * ε k + 9 / 4 * ε k ^ 2)
        ≤ 1 * Real.sqrt (3 * ε k + 9 / 4 * ε k ^ 2) :=
          mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg _)
      _ = Real.sqrt (3 * ε k + 9 / 4 * ε k ^ 2) := one_mul _

/-- Radial secant bounds for $F(u,v)=u^2+|v|$ ($=|u|^2+|v|^1$, a mixed-power gauge objective,
`RadialPower.mixed_powers_radial` with $\psi=0$) on every compact set. -/
theorem uv_radial (K : Set (Vec 2)) (hK : IsCompact K) :
    RadialCertificate.HasRadialSecantBounds UnexcitedMetric.objective K 0 := by
  have habs : ∀ i : Fin 2, ConvexOn ℝ univ (fun x : Vec 2 => |x i|) := by
    intro i
    refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
      _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hsmooth : CenteredSmoothSublinear.LocallyC11On univ (fun _ : Vec 2 => (0 : ℝ)) := by
    refine ⟨differentiableOn_const 0, ?_⟩
    rw [fderiv_const]
    intro x _
    exact ⟨0, univ, Filter.univ_mem, (LipschitzWith.const _).lipschitzOnWith⟩
  refine RadialPower.mixed_powers_radial (Γ := fun i : Fin 2 => fun x : Vec 2 => |x i|)
    UnexcitedMetric.objective_convex habs ?_ (fun j x => abs_nonneg _) ![2, 1] ?_ 0 isOpen_univ
    hsmooth hK (subset_univ K) ?_
  · intro j t ht x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  · intro j
    fin_cases j <;> norm_num
  · intro x _
    simp only [RadialPower.sumObjective, RadialPower.powered, Fin.sum_univ_two, sub_zero,
      UnexcitedMetric.objective, zero_add]
    norm_num [sq_abs]

/-- The radial band certificate for $F(u,v)=u^2+|v|$ on the band $K_\eta$ of a compact $K$:
the continuous field $W(x)=xx^T$ (`rankOneCertificate`, as in
`radial_implies_band_certificates`). -/
def uvCert (K : Set (Vec 2)) (hK : IsCompact K) (c₁ c₂ η : ℝ) (hc₁ : 0 < c₁) (hc₂ : c₂ < 1)
    (hη : 0 < η) :
    BandCertificate UnexcitedMetric.objective K (UnexcitedMetric.objective 0) c₁ c₂ η :=
  rankOneCertificate (fun x => x - 0) (η ^ 2) (uv_radial K hK η hη).choose 0 1
    (sq_pos_of_pos hη) le_rfl one_pos
    (fun x hx g hg => by
      have hs := convex_supporting_inequality UnexcitedMetric.objective_convex hg 0
      have he : dot g (0 - x) = -dot g (x - 0) := by
        unfold dot
        simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [he] at hs
      have hgap : η ≤ dot g (x - 0) := by linarith [hx.2]
      nlinarith)
    (fun x z g h hx hz e _ => by
      have hdec : UnexcitedMetric.objective z ≤ UnexcitedMetric.objective x := by
        have hp := mul_pos hc₁ e.decrease_pos
        linarith [e.armijo]
      exact (uv_radial K hK η hη).choose_spec x z g h hx.1 hz.1 hz.2 hdec e.gradient_x
        e.gradient_z (eligible_curvature_pos e hc₂))
    (fun x z g h _ _ _ _ => ⟨1, 1, by simp only [one_smul, pairStep]; abel, by simp⟩)

/-- The hypotheses of display `disp/019` (and of `disp/020`, `prose/034`-`prose/036`) can all
hold with a nonzero accessible jump. Here there is one accessible jump direction; two independent
ones, as in `prose/050`, occur in the vertex example below, where no certificate can have a
continuous extension. $F(u,v)=u^2+|v|$, $F_*=0$, $K=\{F\le3\}$, $(c_1,c_2)=(1/4,1/2)$,
$\eta=1/2$, the continuous certificate $W(x)=xx^T$ (finite continuous extension $W(p)=pp^T$ at
$p=(1,0)$), and the accessible jump $j=(0,-2)$ along the eligible pairs $x_k=(1,v_k)$,
$z_k=(1,-v_k/3)$, $v_k=1/(k+2)$. (Indeed $W(p)j=0$.) -/
example : ∃ (F : Vec 2 → ℝ) (Fstar b : ℝ) (K : Set (Vec 2)) (c₁ c₂ η : ℝ)
    (Cert : BandCertificate F K Fstar c₁ c₂ η) (p : Vec 2) (Wp : Mat 2) (j : Vec 2),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ K = {x | F x ≤ b} ∧ IsCompact K ∧
      (0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) ∧ 0 < η ∧
      Tendsto Cert.W (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p)
        (𝓝 Wp) ∧
      AccessibleJump F K Fstar c₁ c₂ η p j ∧ j ≠ 0 := by
  have hK : IsCompact {x : Vec 2 | UnexcitedMetric.objective x ≤ 3} :=
    Localization.sublevel_compact UnexcitedMetric.objective_convex 0
      (fun x => by simpa [UnexcitedMetric.objective] using UnexcitedMetric.objective_nonneg x)
      (fun x hx => UnexcitedMetric.unique_minimum hx) 3
  have h0 : UnexcitedMetric.objective 0 = 0 := by simp [UnexcitedMetric.objective]
  have hF : ∀ x : Vec 2, UnexcitedMetric.objective x = x 0 ^ 2 + |x 1| := fun _ => rfl
  let Cert := uvCert {x | UnexcitedMetric.objective x ≤ 3} hK (1 / 4) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  let v : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2)
  have hv : ∀ k, 0 < v k ∧ v k ≤ 1 / 2 := fun k => by
    have : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact ⟨by positivity, by
      simp only [v]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith⟩
  have hvlim : Tendsto v atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, v]
    ring
  let xs : ℕ → Vec 2 := fun k => ![1, v k]
  let zs : ℕ → Vec 2 := fun k => ![1, -v k / 3]
  have hgx : ∀ k, HasFDerivAt UnexcitedMetric.objective (gradientFunctional ![2, 1]) (xs k) := by
    intro k
    have hpos : 0 < (xs k) 1 := by simp [xs, (hv k).1]
    have h := uv_hasGradient _ hF hpos.ne'
    rw [if_pos hpos] at h
    simpa [xs] using h
  have hgz : ∀ k, HasFDerivAt UnexcitedMetric.objective (gradientFunctional ![2, -1]) (zs k) := by
    intro k
    have hneg : (zs k) 1 < 0 := by
      show -v k / 3 < 0
      linarith [(hv k).1]
    have h := uv_hasGradient _ hF hneg.ne
    rw [if_neg (not_lt.mpr hneg.le)] at h
    simpa [zs] using h
  have hd : ∀ k, -dot ![2, 1] (zs k - xs k) = 4 / 3 * v k := fun k => by
    simp [dot, Fin.sum_univ_two, xs, zs]; ring
  have ht : ∀ k, dot (![2, -1] - ![2, 1]) (zs k - xs k) = 8 / 3 * v k := fun k => by
    simp [dot, Fin.sum_univ_two, xs, zs]; ring
  have hFx : ∀ k, UnexcitedMetric.objective (xs k) = 1 + v k := fun k => by
    simp [hF, xs, abs_of_pos (hv k).1]
  have hFz : ∀ k, UnexcitedMetric.objective (zs k) = 1 + v k / 3 := fun k => by
    have : -v k / 3 < 0 := by linarith [(hv k).1]
    simp only [hF, zs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      abs_of_neg this]
    ring
  refine ⟨UnexcitedMetric.objective, UnexcitedMetric.objective 0, 3, _, 1 / 4, 1 / 2, 1 / 2, Cert,
    ![1, 0], outer (![1, 0] - 0) (![1, 0] - 0), ![0, -2], UnexcitedMetric.objective_convex,
    ⟨⟨0, rfl⟩, by rintro _ ⟨x, rfl⟩; rw [h0]; exact UnexcitedMetric.objective_nonneg x⟩, rfl, hK,
    by norm_num, by norm_num, ?_, ?_, ?_⟩
  · have hcont : Continuous Cert.W := by
      change Continuous fun x : Vec 2 => outer (x - 0) (x - 0)
      unfold outer
      fun_prop
    exact (hcont.tendsto _).mono_left nhdsWithin_le_nhds
  · refine ⟨xs, zs, fun _ => ![2, 1], fun _ => ![2, -1], fun k => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩,
      ?_, ?_, ?_, ?_, tendsto_const_nhds.congr fun k => by
        ext i; fin_cases i <;> norm_num⟩
    · show UnexcitedMetric.objective (xs k) ≤ 3
      rw [hFx]; linarith [(hv k).2]
    · show UnexcitedMetric.objective (xs k) ≥ UnexcitedMetric.objective 0 + 1 / 2
      rw [hFx, h0]; linarith [(hv k).1]
    · show UnexcitedMetric.objective (zs k) ≤ 3
      rw [hFz]; linarith [(hv k).2]
    · show UnexcitedMetric.objective (zs k) ≥ UnexcitedMetric.objective 0 + 1 / 2
      rw [hFz, h0]; linarith [(hv k).1]
    · have hvk := (hv k).1
      refine ⟨hgx k, hgz k, ?_, ?_, ?_, ?_⟩
      · change 0 < -dot ![2, 1] (zs k - xs k)
        rw [hd]; positivity
      · change 1 / 4 * -dot ![2, 1] (zs k - xs k) ≤
          UnexcitedMetric.objective (xs k) - UnexcitedMetric.objective (zs k)
        rw [hd, hFx, hFz]; linarith
      · change UnexcitedMetric.objective (xs k) - UnexcitedMetric.objective (zs k) ≤
          -dot ![2, 1] (zs k - xs k)
        rw [hd, hFx, hFz]; linarith
      · change (1 - 1 / 2) * -dot ![2, 1] (zs k - xs k) ≤
          dot (![2, -1] - ![2, 1]) (zs k - xs k)
        rw [hd, ht]; linarith
    · apply tendsto_pi_nhds.mpr
      intro i
      fin_cases i
      · simp [xs]
      · simpa [xs] using hvlim
    · apply tendsto_pi_nhds.mpr
      intro i
      fin_cases i
      · simp [zs]
      · simpa [zs] using (hvlim.neg.div_const 3)
    · simp only [hd]
      have h := hvlim.const_mul (4 / 3 : ℝ)
      rwa [mul_zero] at h
    · simp only [ht]
      have h := hvlim.const_mul (8 / 3 : ℝ)
      rwa [mul_zero] at h
  · intro h
    have := congrFun h 1
    norm_num at this

/-- The objective $F(u,v)=|u|+|v|+(u-1)^2$ of the vertex example: its gradient at a point with
$u\ne0\ne v$ is $(\operatorname{sign}u+2(u-1),\operatorname{sign}v)$ (signs as one-sided
derivatives of $|\cdot|$). -/
theorem vertex_hasGradient (F : Vec 2 → ℝ) (hF : ∀ x, F x = |x 0| + |x 1| + (x 0 - 1) ^ 2)
    {x : Vec 2} {s0 s1 : ℝ} (h0 : HasDerivAt (fun t : ℝ => |t|) s0 (x 0))
    (h1 : HasDerivAt (fun t : ℝ => |t|) s1 (x 1)) :
    HasFDerivAt F (gradientFunctional ![s0 + 2 * (x 0 - 1), s1]) x := by
  have hFe : F = fun x : Vec 2 => |x 0| + |x 1| + (x 0 - 1) ^ 2 := funext hF
  subst hFe
  have p0 : HasFDerivAt (fun x : Vec 2 => x 0) (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 0 x
  have p1 : HasFDerivAt (fun x : Vec 2 => x 1) (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  have hq : HasDerivAt (fun t : ℝ => (t - 1) ^ 2) (2 * (x 0 - 1)) (x 0) := by
    have := (hasDerivAt_pow 2 (x 0 - 1)).comp (x 0) ((hasDerivAt_id (x 0)).sub_const 1)
    simpa [Function.comp_def] using this
  have hsum := ((h0.comp_hasFDerivAt x p0).add (h1.comp_hasFDerivAt x p1)).add
    (hq.comp_hasFDerivAt x p0)
  convert hsum using 1
  ext v
  simp [gradientFunctional_apply, dot, Fin.sum_univ_two]
  ring

/-- $F(u,v)=|u|+|v|+(u-1)^2\ge\frac34$, with equality only at $(\frac12,0)$. -/
theorem vertex_lower (F : Vec 2 → ℝ) (hF : ∀ x, F x = |x 0| + |x 1| + (x 0 - 1) ^ 2) (x : Vec 2) :
    3 / 4 ≤ F x ∧ (F x = 3 / 4 → x = ![1 / 2, 0]) := by
  rw [hF]
  have h1 := abs_nonneg (x 1)
  rcases le_or_lt 0 (x 0) with h0 | h0
  · rw [abs_of_nonneg h0]
    refine ⟨by nlinarith [sq_nonneg (x 0 - 1 / 2)], fun he => ?_⟩
    have hv : |x 1| = 0 := by nlinarith [sq_nonneg (x 0 - 1 / 2)]
    have hu : (x 0 - 1 / 2) ^ 2 = 0 := by nlinarith
    have hu' : x 0 = 1 / 2 := by nlinarith [sq_nonneg (x 0 - 1 / 2)]
    ext i
    fin_cases i
    · simpa using hu'
    · simpa using abs_eq_zero.mp hv
  · rw [abs_of_neg h0]
    refine ⟨by nlinarith, fun he => ?_⟩
    nlinarith

/-- Two linearly independent accessible limiting jumps at a nonoptimal vertex (non-vacuity of
`vertex_obstruction`, hence of the reading of item `C/05_G/prose/050` as an obstruction):
$F(u,v)=|u|+|v|+(u-1)^2$ (finite convex, $F_*=\frac34$ at $(\frac12,0)$), $K=\{F\le2\}$,
$(c_1,c_2)=(1/4,1/2)$, $\eta=1/8$, $p=(0,0)$ ($F(p)=1$). The eligible pairs
$x_k=(v_k,v_k)$, $z_k=(v_k,-v_k/3)$ give the jump $(0,-2)$, and $x_k=(-v_k,v_k)$,
$z_k=(v_k/3,v_k)$ give jumps $(2+\frac83v_k,0)\to(2,0)$, with $v_k=1/(k+8)\to0$. Hence no band
certificate on this band has a finite continuous extension to $p$. -/
example : ∃ (F : Vec 2 → ℝ) (Fstar b : ℝ) (K : Set (Vec 2)) (c₁ c₂ η : ℝ) (p j₁ j₂ : Vec 2),
    ConvexOn ℝ univ F ∧ IsLeast (Set.range F) Fstar ∧ K = {x | F x ≤ b} ∧ IsCompact K ∧
      (0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1) ∧ 0 < η ∧ Fstar < F p ∧
      AccessibleJump F K Fstar c₁ c₂ η p j₁ ∧ AccessibleJump F K Fstar c₁ c₂ η p j₂ ∧
      LinearIndependent ℝ ![euclideanVector j₁, euclideanVector j₂] ∧
      ∀ Cert : BandCertificate F K Fstar c₁ c₂ η, ¬ ∃ Wp : Mat 2,
        Tendsto Cert.W (𝓝[{z | z ∈ positiveBand F K Fstar η ∧ DifferentiableAt ℝ F z}] p)
          (𝓝 Wp) := by
  let F : Vec 2 → ℝ := fun x => |x 0| + |x 1| + (x 0 - 1) ^ 2
  have hF : ∀ x, F x = |x 0| + |x 1| + (x 0 - 1) ^ 2 := fun _ => rfl
  have hconv : ConvexOn ℝ univ F := by
    have habs : ∀ i : Fin 2, ConvexOn ℝ univ (fun x : Vec 2 => |x i|) := by
      intro i
      refine ⟨convex_univ, fun x _ y _ a c ha hc _ => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * x i + c * y i| ≤ |a * x i| + |c * y i| := abs_add_le _ _
        _ = a * |x i| + c * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
    have hsq : ConvexOn ℝ univ (fun x : Vec 2 => (x 0 - 1) ^ 2) := by
      refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hc' : c = 1 - a := by linarith
      subst hc'
      nlinarith [sq_nonneg (x 0 - y 0), mul_nonneg ha hc]
    exact ((habs 0).add (habs 1)).add hsq
  have hval : F ![1 / 2, 0] = 3 / 4 := by
    have h12 : |(1 : ℝ) / 2| = 1 / 2 := abs_of_pos (by norm_num)
    norm_num [F, h12]
  have hmin : ∀ x, F ![1 / 2, 0] ≤ F x := fun x => by
    rw [hval]; exact (vertex_lower F hF x).1
  have huniq : ∀ x, F x = F ![1 / 2, 0] → x = ![1 / 2, 0] := fun x hx => by
    rw [hval] at hx; exact (vertex_lower F hF x).2 hx
  have hK : IsCompact {x | F x ≤ 2} := Localization.sublevel_compact hconv _ hmin huniq 2
  have hFstar : IsLeast (Set.range F) (3 / 4) := by
    refine ⟨⟨![1 / 2, 0], hval⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (vertex_lower F hF x).1
  obtain ⟨v, hv_def⟩ : ∃ v : ℕ → ℝ, v = fun k : ℕ => 1 / ((k : ℝ) + 8) := ⟨_, rfl⟩
  have hv : ∀ k, 0 < v k ∧ v k ≤ 1 / 8 := fun k => by
    have : (8 : ℝ) ≤ (k : ℝ) + 8 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [hv_def]
    exact ⟨by positivity, by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith⟩
  have hvlim : Tendsto v atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 7)
    rw [hv_def]
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, Nat.cast_add]
    norm_num
    ring
  have habs_pos : ∀ {t : ℝ}, 0 < t → HasDerivAt (fun t : ℝ => |t|) 1 t :=
    fun ht => hasDerivAt_abs_pos ht
  have habs_neg : ∀ {t : ℝ}, t < 0 → HasDerivAt (fun t : ℝ => |t|) (-1) t :=
    fun ht => hasDerivAt_abs_neg ht
  have hpt : Tendsto (fun k => (![v k, v k] : Vec 2)) atTop (𝓝 ![0, 0]) := by
    apply tendsto_pi_nhds.mpr
    intro i; fin_cases i <;> simpa using hvlim
  -- the two families of eligible pairs
  let xs1 : ℕ → Vec 2 := fun k => ![v k, v k]
  let zs1 : ℕ → Vec 2 := fun k => ![v k, -v k / 3]
  let g1 : ℕ → Vec 2 := fun k => ![1 + 2 * (v k - 1), 1]
  let h1 : ℕ → Vec 2 := fun k => ![1 + 2 * (v k - 1), -1]
  let xs2 : ℕ → Vec 2 := fun k => ![-v k, v k]
  let zs2 : ℕ → Vec 2 := fun k => ![v k / 3, v k]
  let g2 : ℕ → Vec 2 := fun k => ![-1 + 2 * (-v k - 1), 1]
  let h2 : ℕ → Vec 2 := fun k => ![1 + 2 * (v k / 3 - 1), 1]
  have hgrad : ∀ k, HasFDerivAt F (gradientFunctional (g1 k)) (xs1 k) ∧
      HasFDerivAt F (gradientFunctional (h1 k)) (zs1 k) ∧
      HasFDerivAt F (gradientFunctional (g2 k)) (xs2 k) ∧
      HasFDerivAt F (gradientFunctional (h2 k)) (zs2 k) := by
    intro k
    have hp := (hv k).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact vertex_hasGradient F hF (x := xs1 k) (habs_pos (by simp [xs1, hp]))
        (habs_pos (by simp [xs1, hp]))
    · exact vertex_hasGradient F hF (x := zs1 k) (habs_pos (by simp [zs1, hp]))
        (habs_neg (by simp [zs1]; linarith))
    · exact vertex_hasGradient F hF (x := xs2 k) (habs_neg (by simp [xs2, hp]))
        (habs_pos (by simp [xs2, hp]))
    · exact vertex_hasGradient F hF (x := zs2 k) (habs_pos (by simp [zs2]; linarith))
        (habs_pos (by simp [zs2, hp]))
  have hval1 : ∀ k, F (xs1 k) = 1 + v k ^ 2 ∧ F (zs1 k) = 1 - 2 / 3 * v k + v k ^ 2 := by
    intro k
    have hp := (hv k).1
    have hn : -v k / 3 < 0 := by linarith
    constructor
    · simp only [F, xs1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        abs_of_pos hp]
      ring
    · simp only [F, zs1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        abs_of_pos hp, abs_of_neg hn]
      ring
  have hval2 : ∀ k, F (xs2 k) = 1 + 4 * v k + v k ^ 2 ∧
      F (zs2 k) = 1 + 2 / 3 * v k + v k ^ 2 / 9 := by
    intro k
    have hp := (hv k).1
    have hn : -v k < 0 := by linarith
    have hp3 : 0 < v k / 3 := by linarith
    constructor
    · simp only [F, xs2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        abs_of_pos hp, abs_of_neg hn]
      ring
    · simp only [F, zs2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        abs_of_pos hp, abs_of_pos hp3]
      ring
  have hd1 : ∀ k, -dot (g1 k) (zs1 k - xs1 k) = 4 / 3 * v k := fun k => by
    simp [dot, Fin.sum_univ_two, g1, zs1, xs1]; ring
  have ht1 : ∀ k, dot (h1 k - g1 k) (zs1 k - xs1 k) = 8 / 3 * v k := fun k => by
    simp [dot, Fin.sum_univ_two, g1, h1, zs1, xs1]; ring
  have hd2 : ∀ k, -dot (g2 k) (zs2 k - xs2 k) = 4 * v k + 8 / 3 * v k ^ 2 := fun k => by
    simp [dot, Fin.sum_univ_two, g2, zs2, xs2]; ring
  have ht2 : ∀ k, dot (h2 k - g2 k) (zs2 k - xs2 k) = 8 / 3 * v k + 32 / 9 * v k ^ 2 :=
    fun k => by
      simp [dot, Fin.sum_univ_two, g2, h2, zs2, xs2]; ring
  have hj2 : ∀ k, h2 k - g2 k = ![2 + 8 / 3 * v k, 0] := fun k => by
    ext i; fin_cases i
    · simp [g2, h2]; ring
    · simp [g2, h2]
  have hband : ∀ y : Vec 2, F y ≤ 2 → 3 / 4 + 1 / 8 ≤ F y →
      y ∈ {x | x ∈ {x | F x ≤ 2} ∧ F x ≥ 3 / 4 + 1 / 8} := fun y h1 h2 => ⟨h1, h2⟩
  have hJ1 : AccessibleJump F {x | F x ≤ 2} (3 / 4) (1 / 4) (1 / 2) (1 / 8) ![0, 0] ![0, -2] := by
    refine ⟨xs1, zs1, g1, h1, fun k => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · have := (hv k).2; have := (hv k).1
      exact hband _ (by rw [(hval1 k).1]; nlinarith) (by rw [(hval1 k).1]; nlinarith)
    · have := (hv k).2; have := (hv k).1
      exact hband _ (by rw [(hval1 k).2]; nlinarith) (by rw [(hval1 k).2]; nlinarith)
    · have hp := (hv k).1
      refine ⟨(hgrad k).1, (hgrad k).2.1, ?_, ?_, ?_, ?_⟩
      · change 0 < -dot (g1 k) (zs1 k - xs1 k); rw [hd1]; positivity
      · change 1 / 4 * -dot (g1 k) (zs1 k - xs1 k) ≤ F (xs1 k) - F (zs1 k)
        rw [hd1, (hval1 k).1, (hval1 k).2]; linarith
      · change F (xs1 k) - F (zs1 k) ≤ -dot (g1 k) (zs1 k - xs1 k)
        rw [hd1, (hval1 k).1, (hval1 k).2]; linarith
      · change (1 - 1 / 2) * -dot (g1 k) (zs1 k - xs1 k) ≤ dot (h1 k - g1 k) (zs1 k - xs1 k)
        rw [hd1, ht1]; linarith
    · apply tendsto_pi_nhds.mpr; intro i; fin_cases i <;> simpa [xs1] using hvlim
    · apply tendsto_pi_nhds.mpr; intro i; fin_cases i
      · simpa [zs1] using hvlim
      · simpa [zs1] using hvlim.neg.div_const 3
    · simp only [hd1]; have h := hvlim.const_mul (4 / 3 : ℝ); rwa [mul_zero] at h
    · simp only [ht1]; have h := hvlim.const_mul (8 / 3 : ℝ); rwa [mul_zero] at h
    · refine tendsto_const_nhds.congr fun k => ?_
      ext i; fin_cases i
      · simp [g1, h1]
      · simp [g1, h1]; norm_num
  have hJ2 : AccessibleJump F {x | F x ≤ 2} (3 / 4) (1 / 4) (1 / 2) (1 / 8) ![0, 0] ![2, 0] := by
    refine ⟨xs2, zs2, g2, h2, fun k => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · have := (hv k).2; have := (hv k).1
      exact hband _ (by rw [(hval2 k).1]; nlinarith) (by rw [(hval2 k).1]; nlinarith)
    · have := (hv k).2; have := (hv k).1
      exact hband _ (by rw [(hval2 k).2]; nlinarith) (by rw [(hval2 k).2]; nlinarith)
    · have hp := (hv k).1
      refine ⟨(hgrad k).2.2.1, (hgrad k).2.2.2, ?_, ?_, ?_, ?_⟩
      · change 0 < -dot (g2 k) (zs2 k - xs2 k); rw [hd2]; positivity
      · change 1 / 4 * -dot (g2 k) (zs2 k - xs2 k) ≤ F (xs2 k) - F (zs2 k)
        rw [hd2, (hval2 k).1, (hval2 k).2]; nlinarith
      · change F (xs2 k) - F (zs2 k) ≤ -dot (g2 k) (zs2 k - xs2 k)
        rw [hd2, (hval2 k).1, (hval2 k).2]; nlinarith
      · change (1 - 1 / 2) * -dot (g2 k) (zs2 k - xs2 k) ≤ dot (h2 k - g2 k) (zs2 k - xs2 k)
        rw [hd2, ht2]; nlinarith
    · apply tendsto_pi_nhds.mpr; intro i; fin_cases i
      · simpa [xs2] using hvlim.neg
      · simpa [xs2] using hvlim
    · apply tendsto_pi_nhds.mpr; intro i; fin_cases i
      · simpa [zs2] using hvlim.div_const 3
      · simpa [zs2] using hvlim
    · simp only [hd2]
      have h := (hvlim.const_mul (4 : ℝ)).add ((hvlim.pow 2).const_mul (8 / 3 : ℝ))
      rwa [mul_zero, zero_pow two_ne_zero, mul_zero, add_zero] at h
    · simp only [ht2]
      have h := (hvlim.const_mul (8 / 3 : ℝ)).add ((hvlim.pow 2).const_mul (32 / 9 : ℝ))
      rwa [mul_zero, zero_pow two_ne_zero, mul_zero, add_zero] at h
    · simp only [hj2]
      apply tendsto_pi_nhds.mpr; intro i; fin_cases i
      · have h := (hvlim.const_mul (8 / 3 : ℝ)).const_add 2
        rw [mul_zero, add_zero] at h
        simpa using h
      · simp
  have hind : LinearIndependent ℝ ![euclideanVector (![0, -2] : Vec 2),
      euclideanVector (![2, 0] : Vec 2)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) hst
    have h1 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) hst
    simp [euclideanVector] at h0 h1
    exact ⟨by linarith, by linarith⟩
  exact ⟨F, 3 / 4, 2, _, 1 / 4, 1 / 2, 1 / 8, ![0, 0], ![0, -2], ![2, 0], hconv, hFstar, rfl, hK,
    by norm_num, by norm_num, by norm_num [F], hJ1, hJ2, hind,
    vertex_obstruction hconv (3 / 4) hFstar 2 _ rfl hK (1 / 4) (1 / 2) (by norm_num) (1 / 8)
      (by norm_num) ![0, 0] ![0, -2] ![2, 0] hJ1 hJ2 hind⟩

end BfgsCoverage.Companion.Ch05G
