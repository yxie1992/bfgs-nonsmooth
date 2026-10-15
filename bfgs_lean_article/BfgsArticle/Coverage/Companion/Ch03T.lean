import BfgsArticle.Coverage.Article.Energy
import BfgsVerification.TransportedCertificateVariants
import BfgsVerification.CompactSolutionBasin
import BfgsVerification.ParabolicExampleContrast
import BfgsVerification.AffineCovariance
import BfgsVerification.ComparisonEnergyWarning
import BfgsVerification.ResidualBudget
import BfgsVerification.ScalarTransportEnergy

/-!
# Lean coverage: `companion/chapters/03_T.tex`

Chapter T ("Transported comparison energies"): the objective-pair terminology, the Theorem
"One-sided transported-certificate convergence" (`C/03_T/theorem/001`) with its proof (the
subsection "Proof", lines 120-165), the local and shell variants, the scalar form and the
absorption of a bounded potential, and the comparison with the radial secant condition (RS) of
Chapter R. Register: `editorial/lean_coverage/register/C_03_T.json`.

## Lean forms

The forms of the article's `BfgsCoverage.Article.Energy` are reused. An admissible run is
`R : AdmissibleBFGSRun n F` (`BfgsCoverage.Article.Energy.admissible_iff`), with
$s_k,y_k,t_k,B_k,q_k,d_k$ = `R.displacement k`, `R.gradientChange k`, `R.curvature k`,
`R.hessian k`, `R.q k`, `R.d k`. "$x$ is differentiable with $g=\nabla F(x)$" is
`HasFDerivAt F (gradientFunctional g) x`. The setting of the chapter (lines 36-39) is
`IsLeast (Set.range F) Fstar` ($F_*=\min F$ attained), `hK_def : K = {x | F x ≤ b}`,
`hb : b > Fstar`, `hK : IsCompact K`. The band $K_\eta$ is `{x | x ∈ K ∧ F x ≥ Fstar + η}`. A pair
$x,z$ has $s=z-x$, $y=h-g$, $d=-g^Ts$, $t=y^Ts$ (`pair_notation`); eligibility (3.2) is
`TransportedCertificate.EligiblePair` (`eligible_iff`); $\Pi_s$ is `stepProjector s`
(`projector_display`). The certificate on one band is the library's `BandCertificate` with any real
$C$ ($C_\eta<\infty$; `bandCertificate_iff`), and "every band admits one" is `HasBandCertificates`
(`hasBandCertificates_iff`); the theorem states these conditions written out. The distance to
$\arg\min F$ is Euclidean (`euclideanSolutionDistance`).

## Items

* Setting and terminology (lines 36-74): `min_attained_iff` (disp/001), `run_display`,
  `update_display`, `line_search_display` (disp/002-004), `admissible_run_def` (prose/003),
  `pair_notation` (disp/005-006), `eligible_iff` (disp/007), `accepted_eligible` (prose/006),
  `convexity_upper_bound` (prose/007), `projector_display` (disp/008).
* Theorem (lines 90-111): `one_sided_convergence` (theorem/001, with disp/009-012);
  `condition_readings` (prose/010).
* Proof (lines 120-165): `proof_notation` (disp/013), `hessian_form` (disp/014),
  `annihilated_psd` (disp/015), `annihilation_projection` (disp/016), `armijo_summable`
  (prose/015), `bounded_subgradients` (prose/016), `reciprocal_mean_diverges` (disp/017),
  `energy_nonneg` (disp/018), `trace_recurrence` (disp/019), `normalization` (disp/020),
  `reciprocal_budget` (disp/021).
* The formal route (line 167): `enlarged_recurrence` (prose/017), `quadratic_budget`,
  `quadratic_budget_finite`, `superquadratic_growth` (prose/018), `summable_of_limit` (prose/019),
  `linear_budget` (prose/021).
* Local statement and shells (lines 173-180): `outside_neighborhood_gap` (disp/022),
  `local_basin` (prose/022), `rejected_trial_outside` (prose/023), `solution_set_basin`,
  `structural_region_convergence` (prose/024), `shell_certificates`, `shell_convergence`,
  `shell_band_eq` (prose/025).
* Scalar form (lines 186-202): `rank_one_sufficient` (disp/023), `rank_one_conditions`,
  `rank_one_certificate` (disp/024), `rank_one_degenerate` and `degenerate_multiplier`
  (prose/026; the contrast of the same sentence is prose/043), `certificate_sum` (prose/027),
  `potential_absorption` (prose/028, with disp/025).
* Comparison with RS (lines 216-239): `rs_iff`, `radial_field_energy` (disp/026),
  `radial_visibility` (disp/027), `radial_secant_exact`, `rs_gives_s` and the counterexample
  `s_not_exactly_rs` (prose/029), `radial_projection` (disp/028), `radial_transport_equality`
  (prose/030), `rs_covered` (prose/031), `rs_strictly_weaker` (prose/032),
  `transport_perpendicular` (disp/029), `affine_covariance` (prose/034), `energy_warning`
  (prose/035).

## Discrepancies

Three items of the register are discrepancies; Lean states what holds.
* `C/03_T/prose/029` (line 225, imprecision): "Condition (S) is exactly (RS)". For the radial field
  $W(x)=(x-x_*)(x-x_*)^T$, (S) is the inequality of (RS) restricted to eligible pairs in $K_\eta$
  with $d\le\delta_\eta$: (RS) gives (S) with the same constant (`radial_secant_exact`,
  `rs_gives_s`), but (S) does not give (RS) (`s_not_exactly_rs`, $F(x)=\max\{|x|,2x-1\}$ on $\R$,
  adapted from the independent review's witness).
* `C/03_T/prose/042` (lines 148, 160, 165, typo): the proof cites its equations (3.3)-(3.6) as
  "(3)--(4)", "(6)" and "(5)", numbers that the companion does not print.
* `C/03_T/prose/043` (line 196, typo): "Unlike the preceding moving-frame theorem": the only
  moving-frame theorem before this chapter, Theorem `M:residualtheorem` (`02_M.tex:220-237`),
  requires no invertible transport either; the contrast holds with the moving-frame criterion of
  Section 2.4 (`02_M.tex:196-211`, `BfgsCoverage.Companion.Ch02M.frame_criterion`), which assumes
  bounded inverse norms of the cumulative transports. That the scalar form needs no invertible
  $\lambda$ is `rank_one_degenerate` and `degenerate_multiplier`.

## Standing assumptions inside the proof

The displays of the proof are stated under the hypotheses of the theorem (its certificate
hypothesis as `HasBandCertificates`) and the objects the proof introduces, as variables with
their defining equations (`M`, `ℓ`, `Cert`, `k₀`, `E`, `a`, `P`, `Pbar`). From line 144 on they sit
inside a proof by contradiction ("Suppose the objective gap tends to $\ell>0$"), so their standing
assumptions cannot all hold; each is proved from a general form with satisfiable assumptions
(`trace_step_general`, `C_nonneg_of_pair`, and the article's `certificate_energy_nonneg`,
`normalization_bounds`, `certificate_budget_general`). The companion allows any real $C_\eta$;
display 021 needs $C\ge0$, which (S) forces at the accepted pair $(x_{k_0},x_{k_0+1})$
(`C_nonneg_of_pair`). Hypotheses whose names start with `_` are standing assumptions that a proof
does not use.

## Non-vacuity

The examples at the end show that the hypotheses of the theorem, of the general forms of the
proof displays, of the local statements, of the statements about (RS) (`Example.quad_rs`) and of
the potential absorption can hold, with the article's quadratic example ($F(x)=x^2/2$, the run
$x_k=2^{-k}$, the certificates `quadCert`). The last example exhibits an eligible pair covered by
(S) in the witness `s_not_exactly_rs`.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter BfgsVerification

namespace BfgsCoverage.Companion.Ch03T

/-! ### Helpers -/

/-- `dot` is symmetric. -/
theorem dot_comm' {n : ℕ} (a b : Vec n) : dot a b = dot b a := dotProduct_comm a b

/-- $s^Ts\ne0$ for $s\ne0$. -/
theorem dot_self_ne_zero {n : ℕ} {s : Vec n} (hs : s ≠ 0) : dot s s ≠ 0 := by
  intro h0
  apply hs
  funext i
  have hsum : ∑ j, s j * s j = 0 := h0
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (s j))).mp hsum i
    (Finset.mem_univ i)
  simpa using mul_self_eq_zero.mp hi

/-- The certificate conditions on one band, unfolded (with the band written out): a library
`BandCertificate F K Fstar c₁ c₂ η` is exactly a field `W` and constants `m, C, L, δ` with
$m>0$, $L\ge0$, $\delta>0$, $W(x)\succeq0$ at differentiable points of $K_\eta$,
(V) at every differentiable point of $K_\eta$, and (S), (T) for eligible pairs in $K_\eta$ with
$d\le\delta$. The constant $C$ is any real number ("$C_\eta<\infty$"). -/
theorem bandCertificate_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ η : ℝ) :
    Nonempty (TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η) ↔
      ∃ (W : Vec n → Mat n) (m C L δ : ℝ), 0 < m ∧ 0 ≤ L ∧ 0 < δ ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ g : Vec n,
          HasFDerivAt F (gradientFunctional g) x → dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
          ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
            -dot g (z - x) ≤ δ → dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
          ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
            -dot g (z - x) ≤ δ →
            ((1 + L * -dot g (z - x)) • (TransportedCertificate.stepProjector (z - x) * W x *
                TransportedCertificate.stepProjector (z - x)) -
              TransportedCertificate.stepProjector (z - x) * W z *
                TransportedCertificate.stepProjector (z - x)).PosSemidef) := by
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

/-! ### Section "Algorithm and objective-pair terminology" (lines 35-74) -/

/-- Item `C/03_T/disp/001` (`companion/chapters/03_T.tex:37-39`): the standing setting of the
chapter, "Let $F:\R^n\to\R$ be finite and convex, let $F_*=\min F$ be attained, and let
$K=\{x:F(x)\le b\}$, $b>F_*$, be compact." In Lean: `F : Vec n → ℝ` with
`ConvexOn ℝ Set.univ F`; $K$ is a variable with `hK_def : K = {x | F x ≤ b}`, `hb : b > Fstar`,
`hK : IsCompact K`; "$F_*=\min F$ is attained" is `IsLeast (Set.range F) Fstar`, which unfolds
to: some point has value $F_*$ and every value is $\ge F_*$. -/
theorem min_attained_iff {n : ℕ} (F : Vec n → ℝ) (Fstar : ℝ) :
    IsLeast (Set.range F) Fstar ↔ (∃ x, F x = Fstar) ∧ ∀ x, Fstar ≤ F x := by
  constructor
  · rintro ⟨⟨x, hx⟩, hle⟩
    exact ⟨⟨x, hx⟩, fun z => hle (Set.mem_range_self z)⟩
  · rintro ⟨⟨x, hx⟩, hle⟩
    exact ⟨⟨x, hx⟩, by rintro _ ⟨z, rfl⟩; exact hle z⟩

/-- Item `C/03_T/disp/002` (`companion/chapters/03_T.tex:41-44`): "Ordinary full BFGS uses
differentiable accepted endpoints,
\[ g_k=\nabla F(x_k),\quad s_k=-\alpha_kH_kg_k,\quad x_{k+1}=x_k+s_k,\quad y_k=g_{k+1}-g_k \]".
Every admissible run (`AdmissibleBFGSRun`, Definition `art:admissible` of the article;
`BfgsCoverage.Article.Energy.admissible_iff`) satisfies these equations, with the library's
names $s_k$ = `R.displacement k`, $y_k$ = `R.gradientChange k`; "$x_k$ is a differentiable point
with $g_k=\nabla F(x_k)$" is `HasFDerivAt F (gradientFunctional (R.g k)) (R.x k)`. -/
theorem run_display {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    HasFDerivAt F (gradientFunctional (R.g k)) (R.x k) ∧
      R.displacement k = -R.α k • (R.H k *ᵥ R.g k) ∧
      R.x (k + 1) = R.x k + R.displacement k ∧
      R.gradientChange k = R.g (k + 1) - R.g k :=
  ⟨R.hasGradient k, rfl, R.step k, rfl⟩

/-- Item `C/03_T/disp/003` (`companion/chapters/03_T.tex:46-49`): "with $H_0\succ0$,
$\alpha_k>0$, and
\[ H_{k+1}=(I-s_ky_k^T/t_k)H_k(I-y_ks_k^T/t_k)+s_ks_k^T/t_k,\qquad t_k=y_k^Ts_k. \]"
Every admissible run satisfies these conditions; $t_k$ = `R.curvature k`, and $t_k>0$
(`R.curvature_pos`), so `(R.curvature k)⁻¹` is $1/t_k$. -/
theorem update_display {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (R.H 0).PosDef ∧ ∀ k, 0 < R.α k ∧
      R.H (k + 1) = (1 - (R.curvature k)⁻¹ • outer (R.displacement k) (R.gradientChange k)) *
          R.H k * (1 - (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.displacement k)) +
        (R.curvature k)⁻¹ • outer (R.displacement k) (R.displacement k) ∧
      R.curvature k = dot (R.gradientChange k) (R.displacement k) ∧ 0 < R.curvature k :=
  ⟨R.initial_posDef, fun k => ⟨R.alpha_pos k, R.update k, rfl, R.curvature_pos k⟩⟩

/-- Item `C/03_T/disp/004` (`companion/chapters/03_T.tex:51-54`): "The fixed
Armijo--weak-Wolfe conditions are
\[ F(x_{k+1})\le F(x_k)+c_1g_k^Ts_k,\qquad g_{k+1}^Ts_k\ge c_2g_k^Ts_k,\qquad 0<c_1<c_2<1. \]"
These are the fields of every admissible run (fixed constants `R.c₁`, `R.c₂`). -/
theorem line_search_display {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    (0 < R.c₁ ∧ R.c₁ < R.c₂ ∧ R.c₂ < 1) ∧ ∀ k,
      F (R.x (k + 1)) ≤ F (R.x k) + R.c₁ * dot (R.g k) (R.displacement k) ∧
        dot (R.g (k + 1)) (R.displacement k) ≥ R.c₂ * dot (R.g k) (R.displacement k) :=
  ⟨⟨R.c₁_pos, R.c₁_lt_c₂, R.c₂_lt_one⟩, fun k => ⟨R.armijo k, R.weak_wolfe k⟩⟩

/-- Item `C/03_T/prose/003` (`companion/chapters/03_T.tex:55-55`): "An infinite admissible run
has nonzero gradients and well-defined accepted steps." The definition is the library structure
`AdmissibleBFGSRun` (see `BfgsCoverage.Article.Energy.admissible_iff`). Its gradients are nonzero,
every accepted step is nonzero and has $t_k>0$, so the update is well defined, and
$H_k\succ0$ for every $k$. -/
theorem admissible_run_def {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.g k ≠ 0 ∧ R.displacement k ≠ 0 ∧ 0 < R.curvature k ∧ (R.H k).PosDef :=
  ⟨R.gradient_nonzero k, R.accepted_displacement_ne_zero k, R.curvature_pos k,
    R.positive_definite k⟩

/-- Item `C/03_T/disp/005` (`companion/chapters/03_T.tex:58-60`) and the following display
(lines 61-63): for differentiable endpoints $x,z$ with $g=\nabla F(x)$, $h=\nabla F(z)$,
\[ y=h-g,\quad s=z-x,\quad d=-g^Ts,\quad\Delta=F(x)-F(z),\quad t=y^Ts. \]
The library's pair quantities are exactly these: `pairStep x z` $=s$,
`pairDecrease x z g` $=d$, `pairCurvature x z g h` $=t$. -/
theorem pair_notation {n : ℕ} (x z g h : Vec n) :
    TransportedCertificate.pairStep x z = z - x ∧
      TransportedCertificate.pairDecrease x z g = -dot g (z - x) ∧
      TransportedCertificate.pairCurvature x z g h = dot (h - g) (z - x) :=
  ⟨rfl, rfl, rfl⟩

/-- Item `C/03_T/disp/007`, equation (3.2) (`companion/chapters/03_T.tex:65-67`): "Call the
pair eligible if $d>0$, $c_1d\le\Delta\le d$, $t\ge(1-c_2)d$." The library's
`EligiblePair F c₁ c₂ x z g h` is exactly this condition for differentiable endpoints $x,z$ with
gradients $g,h$ (the quantities of the displays at lines 58-63 as variables with their
defining equations). -/
theorem eligible_iff {n : ℕ} (F : Vec n → ℝ) (c₁ c₂ : ℝ) (x z g h : Vec n)
    (s y : Vec n) (hs : s = z - x) (hy : y = h - g) (d Δ t : ℝ) (hd : d = -dot g s)
    (hΔ : Δ = F x - F z) (ht : t = dot y s) :
    TransportedCertificate.EligiblePair F c₁ c₂ x z g h ↔
      (HasFDerivAt F (gradientFunctional g) x ∧ HasFDerivAt F (gradientFunctional h) z) ∧
        d > 0 ∧ c₁ * d ≤ Δ ∧ Δ ≤ d ∧ t ≥ (1 - c₂) * d :=
  BfgsCoverage.Article.Energy.eligiblePair_iff F c₁ c₂ x z g h s y hs hy d Δ t hd hΔ ht

/-- Item `C/03_T/prose/006` (`companion/chapters/03_T.tex:68-68`): "Every accepted step is
eligible." For every admissible run and every $k$, the pair $(x_k,x_{k+1})$ with gradients
$(g_k,g_{k+1})$ is eligible for the run's constants, and its $d$ and $t$ are $d_k$ and $t_k$. -/
theorem accepted_eligible {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    TransportedCertificate.EligiblePair F R.c₁ R.c₂ (R.x k) (R.x (k + 1)) (R.g k) (R.g (k + 1)) ∧
      -dot (R.g k) (R.x (k + 1) - R.x k) = R.d k ∧
      dot (R.g (k + 1) - R.g k) (R.x (k + 1) - R.x k) = R.curvature k :=
  ⟨R.accepted_pair_eligible k, R.accepted_pair_decrease k, R.accepted_pair_curvature k⟩

/-- Item `C/03_T/prose/007` (`companion/chapters/03_T.tex:68-68`): "The upper bound
$\Delta\le d$ follows from convexity." For finite convex $F$, a differentiable point $x$ with
$g=\nabla F(x)$ and any $z$: $F(x)-F(z)\le-g^T(z-x)$. -/
theorem convexity_upper_bound {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (x z g : Vec n) (hg : HasFDerivAt F (gradientFunctional g) x) :
    F x - F z ≤ -dot g (z - x) := by
  have h := convex_supporting_inequality hF hg z
  linarith

/-- Item `C/03_T/disp/008` (`companion/chapters/03_T.tex:71-73`): "For $s\ne0$, define the
Euclidean orthogonal projector $\Pi_s=I-\frac{ss^T}{s^Ts}$." The library's `stepProjector s` is
this matrix, and for $s\ne0$ it is the Euclidean orthogonal projector onto $s^\perp$: symmetric,
idempotent, $\Pi_ss=0$ and $\Pi_sv=v$ whenever $v^Ts=0$. -/
theorem projector_display {n : ℕ} (s : Vec n) :
    TransportedCertificate.stepProjector s = 1 - (dot s s)⁻¹ • outer s s ∧
      (s ≠ 0 → (TransportedCertificate.stepProjector s).IsSymm ∧
        TransportedCertificate.stepProjector s * TransportedCertificate.stepProjector s =
          TransportedCertificate.stepProjector s ∧
        TransportedCertificate.stepProjector s *ᵥ s = 0 ∧
        ∀ v : Vec n, dot v s = 0 → TransportedCertificate.stepProjector s *ᵥ v = v) := by
  have hdef := BfgsCoverage.Article.Energy.stepProjector_eq s
  refine ⟨hdef, fun hs => ⟨TransportedCertificate.stepProjector_isSymm s, ?_,
    TransportedCertificate.stepProjector_mulVec_self s,
    fun v hv => TransportedCertificate.stepProjector_fixes_perpendicular s v hv⟩⟩
  have hσ := dot_self_ne_zero hs
  rw [hdef, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, Matrix.smul_mul,
    Matrix.mul_smul, BFGSCompression.outer_mul_outer, smul_smul, smul_smul]
  have h2 : (dot s s)⁻¹ * (dot s s)⁻¹ * dot s s = (dot s s)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hσ, mul_one]
  rw [h2]
  abel

/-! ### Theorem "One-sided transported-certificate convergence" (lines 90-111) -/

/-- The certificate hypothesis of the theorem, for every band at once: it is the library's
`HasBandCertificates F K Fstar c₁ c₂` (the proof displays below use that name), written out with
`bandCertificate_iff`. -/
theorem hasBandCertificates_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar c₁ c₂ : ℝ) :
    TransportedCertificate.HasBandCertificates F K Fstar c₁ c₂ ↔
      ∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
        ∃ (W : Vec n → Mat n) (m C L δ : ℝ), 0 < m ∧ 0 ≤ L ∧ 0 < δ ∧
          (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
          (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ g : Vec n,
            HasFDerivAt F (gradientFunctional g) x → dot g (W x *ᵥ g) ≥ m) ∧
          (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
            ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
              -dot g (z - x) ≤ δ → dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) ∧
          (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
            ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
              -dot g (z - x) ≤ δ →
              ((1 + L * -dot g (z - x)) • (TransportedCertificate.stepProjector (z - x) * W x *
                  TransportedCertificate.stepProjector (z - x)) -
                TransportedCertificate.stepProjector (z - x) * W z *
                  TransportedCertificate.stepProjector (z - x)).PosSemidef) := by
  constructor
  · intro h η hη hne
    exact (bandCertificate_iff F K Fstar c₁ c₂ η).mp (h η hη hne)
  · intro h η hη hne
    exact (bandCertificate_iff F K Fstar c₁ c₂ η).mpr (h η hη hne)

/-- Item `C/03_T/theorem/001` (`companion/chapters/03_T.tex:90-111`), Theorem "One-sided
transported-certificate convergence", with its displays `C/03_T/disp/009`-`disp/012`.

In the setting of lines 36-39 ($F$ finite convex, $F_*=\min F$ attained,
$K=\{x:F(x)\le b\}$ compact, $b>F_*$): for each $\eta>0$ with nonempty band
$K_\eta=\{x\in K:F(x)\ge F_*+\eta\}$, suppose there is a finite-valued symmetric
positive-semidefinite field $W_\eta(x)$ on differentiable points of $K_\eta$, and constants
$m_\eta>0$, $C_\eta<\infty$, $L_\eta\ge0$, $\delta_\eta>0$ with
\[ g^TW_\eta(x)g\ge m_\eta,\qquad y^TW_\eta(z)y\le C_\eta t,\qquad
   \Pi_sW_\eta(z)\Pi_s\preceq(1+L_\eta d)\Pi_sW_\eta(x)\Pi_s, \]
the last two only for eligible pairs $x,z\in K_\eta$ with $d\le\delta_\eta$. Then every infinite
admissible full-BFGS run starting in $K$ satisfies $F(x_k)\to F_*$ and
$\operatorname{dist}(x_k,\arg\min F)\to0$; if the minimizer is unique, the entire iterate
sequence converges to it.

Readings: the field is `W : Vec n → Mat n` (real entries: finite-valued), `PosSemidef` (which
includes symmetry) at the differentiable points of $K_\eta$; (V) holds at every differentiable
point of $K_\eta$ with $g=\nabla F(x)$; $C$ is any real number; the pair quantities are
$s=z-x$, $y=h-g$, $d=-g^Ts$, $t=y^Ts$; $A\preceq B$ is `(B - A).PosSemidef`; eligibility is for
the run's fixed constants `R.c₁`, `R.c₂`; the distance is Euclidean
(`euclideanSolutionDistance`). Convexity of $F$ is part of the run (`R.convex`). The library
proves this as `transportedCertificateConvergence`. -/
theorem one_sided_convergence {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (hcert : ∀ η : ℝ, 0 < η → {x | x ∈ K ∧ F x ≥ Fstar + η}.Nonempty →
      ∃ (W : Vec n → Mat n) (m C L δ : ℝ), 0 < m ∧ 0 ≤ L ∧ 0 < δ ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, DifferentiableAt ℝ F x → (W x).PosSemidef) ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ g : Vec n,
          HasFDerivAt F (gradientFunctional g) x → dot g (W x *ᵥ g) ≥ m) ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
          ∀ g h : Vec n, TransportedCertificate.EligiblePair F R.c₁ R.c₂ x z g h →
            -dot g (z - x) ≤ δ → dot (h - g) (W z *ᵥ (h - g)) ≤ C * dot (h - g) (z - x)) ∧
        (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
          ∀ g h : Vec n, TransportedCertificate.EligiblePair F R.c₁ R.c₂ x z g h →
            -dot g (z - x) ≤ δ →
            ((1 + L * -dot g (z - x)) • (TransportedCertificate.stepProjector (z - x) * W x *
                TransportedCertificate.stepProjector (z - x)) -
              TransportedCertificate.stepProjector (z - x) * W z *
                TransportedCertificate.stepProjector (z - x)).PosSemidef))
    (hx0 : R.x 0 ∈ K) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 Fstar) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ∀ xstar : Vec n, (∀ x, F xstar ≤ F x) → (∀ x, (∀ z, F x ≤ F z) → x = xstar) →
        Tendsto R.x atTop (𝓝 xstar) := by
  have hlib : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂ :=
    (hasBandCertificates_iff F K Fstar R.c₁ R.c₂).mpr hcert
  obtain ⟨xs, hxs⟩ := hFstar.1
  have hmin : ∀ x, F xs ≤ F x := fun x => hxs ▸ hFstar.2 (Set.mem_range_self x)
  subst hK_def
  have hconv := transportedCertificateConvergence R b hK xs hmin hx0 (hxs ▸ hlib)
  rw [hxs] at hconv
  refine ⟨hconv.1, hconv.2.1, fun xstar hxstar huniq => ?_⟩
  have hFx : F xstar = Fstar :=
    le_antisymm (hxs ▸ hxstar xs) (hFstar.2 (Set.mem_range_self _))
  have h := transportedCertificateConvergence R b hK xstar hxstar hx0 (hFx ▸ hlib)
  exact h.2.2 fun x hx => huniq x fun z => by rw [hx]; exact hxstar z

/-- Item `C/03_T/prose/010` (`companion/chapters/03_T.tex:112-112`): "Condition (V) says that
the comparison directions retain a nonzero component of the gradient on a positive band.
Condition (S) controls the secant correction in those directions. Condition (T) controls their
expansion only in directions perpendicular to the proposed step." Made precise: (V) with $m>0$
forces $W(x)g\ne0$ (for PSD $W$: $g$ has a nonzero component in the range of $W$, the
comparison directions); for $t>0$, (S) is exactly the bound $y^TW(z)y/t\le C$ on the secant
correction of the energy recurrence (3.6); and for symmetric $W(x),W(z)$, (T) is exactly the
comparison $a^TW(z)a\le(1+Ld)\,a^TW(x)a$ on the vectors $a$ with $a^Ts=0$. -/
theorem condition_readings {n : ℕ} (Wx Wz : Mat n) (g y s : Vec n) (m C L d t : ℝ) :
    (0 < m → dot g (Wx *ᵥ g) ≥ m → Wx *ᵥ g ≠ 0) ∧
      (0 < t → (dot y (Wz *ᵥ y) ≤ C * t ↔ dot y (Wz *ᵥ y) / t ≤ C)) ∧
      (Wx.IsSymm → Wz.IsSymm →
        (((1 + L * d) • (TransportedCertificate.stepProjector s * Wx *
            TransportedCertificate.stepProjector s) -
          TransportedCertificate.stepProjector s * Wz *
            TransportedCertificate.stepProjector s).PosSemidef ↔
          ∀ a : Vec n, dot a s = 0 → dot a (Wz *ᵥ a) ≤ (1 + L * d) * dot a (Wx *ᵥ a))) := by
  refine ⟨fun hm hV h0 => ?_, fun ht => (div_le_iff₀ ht).symm, fun hx hz =>
    TransportedCertificate.projected_transport_iff_perpendicular Wx Wz hx hz s (1 + L * d)⟩
  have h : dot g (Wx *ᵥ g) = 0 := by rw [h0]; simp [dot]
  linarith

/-! ### The proof of the theorem (subsection "Proof", lines 120-165)

The displays are stated under the hypotheses of the theorem (with its certificate hypothesis as
`HasBandCertificates`, equivalent by `hasBandCertificates_iff`) and the objects introduced by
the proof, as variables with their defining equations: `M` for $M_k$ (line 132), and, from line
144 on, `ℓ` (the limiting gap, assumed positive), `Cert` (the field of the band $K_{\ell/2}$,
with constants `Cert.m`, `Cert.C`, `Cert.L`, `Cert.δ`), `k₀`, `E`, `a`, `P`, `Pbar`. From line
144 on the standing assumptions are those of a proof by contradiction and cannot all hold; each
such display is also proved in a general form (`..._general`, or the article's
`certificate_step_general` and `certificate_budget_general`) that assumes only band membership of
the iterates involved, and whose assumptions are satisfiable (examples at the end). -/

/-- Item `C/03_T/disp/013` (`companion/chapters/03_T.tex:122-125`): "Put $B_k=H_k^{-1}$,
$q_k=g_k^TH_kg_k$, $d_k=\alpha_kq_k$." The library names are `R.hessian k`, `R.q k`, `R.d k`. -/
theorem proof_notation {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (k : ℕ) :
    R.hessian k = (R.H k)⁻¹ ∧ R.q k = dot (R.g k) (R.H k *ᵥ R.g k) ∧ R.d k = R.α k * R.q k :=
  ⟨rfl, rfl, rfl⟩

/-- Item `C/03_T/disp/014`, equation (3.3) (`companion/chapters/03_T.tex:127-129`): "The
ordinary Hessian update is
\[ B_{k+1}=B_k-\frac{g_kg_k^T}{q_k}+\frac{y_ky_k^T}{t_k}. \]" -/
theorem hessian_form {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ) (_hFstar : IsLeast (Set.range F) Fstar)
    (b : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar)
    (_hK : IsCompact K) (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (_hx0 : R.x 0 ∈ K) (k : ℕ) :
    R.hessian (k + 1) = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) +
      (R.curvature k)⁻¹ • outer (R.gradientChange k) (R.gradientChange k) :=
  R.hessian_update k

/-- Item `C/03_T/disp/015` (`companion/chapters/03_T.tex:131-133`): "Its first two terms form a
PSD matrix $M_k=B_k-g_kg_k^T/q_k\succeq0$, by metric Cauchy--Schwarz." -/
theorem annihilated_psd {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (_hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (_hx0 : R.x 0 ∈ K) (M : ℕ → Mat n)
    (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ) :
    (M k).PosSemidef := by
  rw [hM k]
  exact R.annihilated_hessian_posSemidef k

/-- Item `C/03_T/disp/016`, equation (3.4) (`companion/chapters/03_T.tex:135-137`):
\[ M_ks_k=0,\qquad M_k=\Pi_{s_k}M_k\Pi_{s_k}. \] -/
theorem annihilation_projection {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (_hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (_hx0 : R.x 0 ∈ K) (M : ℕ → Mat n)
    (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ) :
    M k *ᵥ R.displacement k = 0 ∧
      M k = TransportedCertificate.stepProjector (R.displacement k) * M k *
        TransportedCertificate.stepProjector (R.displacement k) := by
  have hker : M k *ᵥ R.displacement k = 0 := by
    rw [hM k]
    exact R.annihilated_hessian_mul_displacement k
  have hsymm : (M k).IsSymm := by
    rw [hM k]
    exact R.annihilated_hessian_isSymm k
  exact ⟨hker, (TransportedCertificate.annihilated_projector (M k) hsymm _ hker).symm⟩

/-- Item `C/03_T/prose/015` (`companion/chapters/03_T.tex:140-140`): "Armijo implies
$\sum d_k<\infty$." For an admissible run whose values are bounded below (here by $F_*$),
the Armijo decreases $c_1d_k\le F(x_k)-F(x_{k+1})$ telescope, so $\sum_kd_k<\infty$. -/
theorem armijo_summable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (Fstar : ℝ)
    (hlow : ∀ k, Fstar ≤ F (R.x k)) : Summable R.d :=
  R.summable_predicted_decreases_of_lower_bound Fstar hlow

/-- Item `C/03_T/prose/016` (`companion/chapters/03_T.tex:140-140`): "a finite convex function
has uniformly bounded subgradients on a compact set". For finite convex $F$ and compact $K$ there
is $G$ with $\|g\|\le G$ (Euclidean norm) for every $x\in K$ and every subgradient $g$ of $F$ at
$x$ ($F(y)\ge F(x)+g^T(y-x)$ for all $y$). In particular the gradients of a run that stays in $K$
are bounded. -/
theorem bounded_subgradients {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ G : ℝ, ∀ x ∈ K, ∀ g : Vec n, (∀ y, dot g (y - x) ≤ F y - F x) →
      ‖euclideanVector g‖ ≤ G := by
  obtain ⟨G, hG, hbound⟩ := convex_supporting_bound_on_compact hF hK
  refine ⟨G, fun x hx g hg => ?_⟩
  have h := hbound x hx g hg
  rw [← BfgsCoverage.Article.Energy.norm_sq_eq_sqNorm] at h
  exact (sq_le_sq₀ (norm_nonneg _) hG.le).mp h

/-- The iterates of a run starting in $K=\{F\le b\}$ stay in $K$ (Armijo), so their gradients are
bounded and $\sum d_k<\infty$ (the facts of line 140 for the actual run). -/
theorem run_bounds {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar)
    (b : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R : AdmissibleBFGSRun n F) (hx0 : R.x 0 ∈ K) :
    (∀ k, R.x k ∈ K) ∧ (∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (R.g k) ≤ G ^ 2) ∧ Summable R.d := by
  have hxK : ∀ k, R.x k ∈ K := by
    intro k
    subst hK_def
    exact (R.objective_le_initial k).trans hx0
  exact ⟨hxK, R.bounded_gradients_of_compact_set K hK hxK,
    R.summable_predicted_decreases_of_lower_bound Fstar
      (fun k => hFstar.2 (Set.mem_range_self _))⟩

/-- Item `C/03_T/disp/017`, equation (3.5) (`companion/chapters/03_T.tex:141-143`): under the
hypotheses of the theorem, "the shared foundation in Chapter~M applies and gives
\[ \frac1N\sum_{k<N}\frac1{q_k}\longrightarrow\infty." \]
(Bounded gradients and $d_k\to0$, from `run_bounds`, and Theorem `M:average`, the article's
Theorem `art:reciprocal-growth`, library `objectiveReciprocalGrowth`.) -/
theorem reciprocal_mean_diverges {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (hx0 : R.x 0 ∈ K) :
    Tendsto (fun N : ℕ => 1 / (N : ℝ) * ∑ k ∈ Finset.range N, (R.q k)⁻¹) atTop atTop := by
  obtain ⟨-, ⟨G, hG, hg⟩, hsum⟩ := run_bounds Fstar hFstar b K hK_def hK R hx0
  have h := (objectiveReciprocalGrowth n F R G hG hg hsum.tendsto_atTop_zero).2
  refine h.congr fun N => ?_
  rw [reciprocalMean, div_eq_inv_mul, one_div]

/-- The tail of line 144 ("Suppose the objective gap tends to $\ell>0$. Use the field for
$\eta=\ell/2$. On a tail $k\ge k_0$, all pairs lie in the band and $d_k\le\delta_\eta$.") exists:
all iterates lie in $K_{\ell/2}$ and, by $\sum d_k<\infty$, some $k_0$ has $d_k\le\delta$ for
$k\ge k_0$. (Undisplayed step; not a register item.) -/
theorem tail_exists {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ) (hFstar : IsLeast (Set.range F) Fstar)
    (b : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (R : AdmissibleBFGSRun n F)
    (hx0 : R.x 0 ∈ K) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ))
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ (ℓ / 2)) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + ℓ / 2} ∧
      R.x (k + 1) ∈ {x | x ∈ K ∧ F x ≥ Fstar + ℓ / 2} ∧ R.d k ≤ Cert.δ := by
  have hsum : Summable R.d :=
    R.summable_predicted_decreases_of_lower_bound Fstar fun k => hFstar.2 (Set.mem_range_self _)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (eventually_le_nhds Cert.delta_pos))
  exact ⟨k₀, fun k hk => ⟨BfgsCoverage.Article.Energy.iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ
    hlim k, BfgsCoverage.Article.Energy.iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim (k + 1),
    hk₀ k hk⟩⟩

/-- Item `C/03_T/disp/018` (`companion/chapters/03_T.tex:145-147`): "Suppress $\eta$ and set
$E_k=\tr(B_kW(x_k))\ge0$, $a_k=1+Ld_k$." Standing assumptions: those of the theorem, the
limiting gap $\lim_k(F(x_k)-F_*)=\ell>0$, the certificate `Cert` of $K_{\ell/2}$, a tail
$k\ge k_0$ with $d_k\le\delta$, and $E_k$, $a_k$ as variables with their defining equations.
Then $E_k\ge0$ for $k\ge k_0$. (General form: the article's `certificate_energy_nonneg`, which
needs only $x_k\in K_\eta$.) -/
theorem energy_nonneg {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (_hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (hx0 : R.x 0 ∈ K) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ))
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ (ℓ / 2))
    (k₀ : ℕ) (_hk₀ : ∀ k, k₀ ≤ k → R.d k ≤ Cert.δ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (a : ℕ → ℝ) (_ha : ∀ k, a k = 1 + Cert.L * R.d k) :
    ∀ k, k₀ ≤ k → 0 ≤ E k := by
  intro k _
  rw [hE k]
  exact BfgsCoverage.Article.Energy.certificate_energy_nonneg R K Fstar (ℓ / 2) Cert k
    (BfgsCoverage.Article.Energy.iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim k)

/-- The trace recurrence (3.6) for one index $k$ (general form of display `C/03_T/disp/019`),
assuming only a certificate on some band $K_\eta$, $x_k,x_{k+1}\in K_\eta$ and $d_k\le\delta$:
\[ E_{k+1}=\tr(M_kW(x_{k+1}))+y_k^TW(x_{k+1})y_k/t_k\le a_k\tr(M_kW(x_k))+C
   =a_k\Bigl(E_k-\frac{g_k^TW(x_k)g_k}{q_k}\Bigr)+C\le a_k(E_k-m/q_k)+C. \]
$C$ may be any real number. -/
theorem trace_step_general {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (a : ℕ → ℝ) (ha : ∀ k, a k = 1 + Cert.L * R.d k)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) (k : ℕ)
    (hxk : R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hxk1 : R.x (k + 1) ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) (hdk : R.d k ≤ Cert.δ) :
    E (k + 1) = (M k * Cert.W (R.x (k + 1))).trace +
        dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) / R.curvature k ∧
      (M k * Cert.W (R.x (k + 1))).trace +
          dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) /
            R.curvature k ≤
        a k * (M k * Cert.W (R.x k)).trace + Cert.C ∧
      a k * (M k * Cert.W (R.x k)).trace + Cert.C =
        a k * (E k - dot (R.g k) (Cert.W (R.x k) *ᵥ R.g k) / R.q k) + Cert.C ∧
      a k * (E k - dot (R.g k) (Cert.W (R.x k) *ᵥ R.g k) / R.q k) + Cert.C ≤
        a k * (E k - Cert.m / R.q k) + Cert.C := by
  obtain ⟨h1, h2, -⟩ := BfgsCoverage.Article.Energy.certificate_step_general R K Fstar η Cert E hE M
    hM k hxk hxk1 hdk
  have htr : (M k * Cert.W (R.x k)).trace =
      E k - dot (R.g k) (Cert.W (R.x k) *ᵥ R.g k) / R.q k := by
    rw [hM k, hE k, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      TransportedCertificate.trace_outer_mul, smul_eq_mul, div_eq_inv_mul]
    rfl
  have hV := Cert.visibility _ hxk (R.g k) (R.hasGradient k)
  have hq := R.q_pos k
  have hdiv : Cert.m / R.q k ≤ dot (R.g k) (Cert.W (R.x k) *ᵥ R.g k) / R.q k :=
    div_le_div_of_nonneg_right hV hq.le
  have hapos : 0 ≤ a k := by
    rw [ha k]
    exact add_nonneg zero_le_one (mul_nonneg Cert.L_nonneg (R.d_pos k).le)
  refine ⟨h1, by rw [ha k]; exact h2, by rw [htr], ?_⟩
  have := mul_le_mul_of_nonneg_left (sub_le_sub_left hdiv (E k)) hapos
  linarith

/-- Item `C/03_T/disp/019`, equation (3.6) (`companion/chapters/03_T.tex:149-155`): "Using
(3)--(4), the Loewner inequality (T), and (S),
\[ E_{k+1}=\tr(M_kW(x_{k+1}))+y_k^TW(x_{k+1})y_k/t_k\le a_k\tr(M_kW(x_k))+C
   =a_k\Bigl(E_k-\frac{g_k^TW(x_k)g_k}{q_k}\Bigr)+C\le a_k(E_k-m/q_k)+C." \]
Under the standing assumptions of display `C/03_T/disp/018` (and $M_k$ of line 132), for every
$k\ge k_0$. These assumptions are jointly inconsistent (the theorem shows that the gap tends to
$0$); the proof uses only `trace_step_general`, whose assumptions are satisfiable. ("(3)--(4)" in
the lead-in, line 148, means (3.3)-(3.4), `hessian_form` and `annihilation_projection`: a typo,
recorded as item `C/03_T/prose/042`.) -/
theorem trace_recurrence {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (_hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (_hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (hx0 : R.x 0 ∈ K) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ))
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ (ℓ / 2))
    (k₀ : ℕ) (hk₀ : ∀ k, k₀ ≤ k → R.d k ≤ Cert.δ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (a : ℕ → ℝ) (ha : ∀ k, a k = 1 + Cert.L * R.d k)
    (M : ℕ → Mat n) (hM : ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) :
    ∀ k, k₀ ≤ k →
      E (k + 1) = (M k * Cert.W (R.x (k + 1))).trace +
          dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) /
            R.curvature k ∧
        (M k * Cert.W (R.x (k + 1))).trace +
            dot (R.gradientChange k) (Cert.W (R.x (k + 1)) *ᵥ R.gradientChange k) /
              R.curvature k ≤
          a k * (M k * Cert.W (R.x k)).trace + Cert.C ∧
        a k * (M k * Cert.W (R.x k)).trace + Cert.C =
          a k * (E k - dot (R.g k) (Cert.W (R.x k) *ᵥ R.g k) / R.q k) + Cert.C ∧
        a k * (E k - dot (R.g k) (Cert.W (R.x k) *ᵥ R.g k) / R.q k) + Cert.C ≤
          a k * (E k - Cert.m / R.q k) + Cert.C :=
  fun k hk => trace_step_general R K Fstar (ℓ / 2) Cert E hE a ha M hM k
    (BfgsCoverage.Article.Energy.iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim k)
    (BfgsCoverage.Article.Energy.iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim (k + 1))
    (hk₀ k hk)

/-- Item `C/03_T/disp/020` (`companion/chapters/03_T.tex:157-159`): "Let $P_{k_0}=1$,
$P_{k+1}=P_ka_k$. Since $\sum d_k<\infty$,
\[ 1\le P_k\le\exp\Bigl(L\sum_{j\ge k_0}d_j\Bigr)=:\overline P<\infty." \]
Under the standing assumptions of display `C/03_T/disp/018`, with $P$ and $\overline P$
(`Pbar`) as variables with their defining equations, for every $k\ge k_0$ ($\overline P$ is a
real number, so $\overline P<\infty$). General form: the article's `normalization_bounds`
(only $L\ge0$ and $\sum d_k<\infty$). -/
theorem normalization {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (_hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (_hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (_hx0 : R.x 0 ∈ K) (ℓ : ℝ) (_hℓ : 0 < ℓ)
    (_hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ))
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ (ℓ / 2))
    (k₀ : ℕ) (_hk₀ : ∀ k, k₀ ≤ k → R.d k ≤ Cert.δ)
    (a : ℕ → ℝ) (ha : ∀ k, a k = 1 + Cert.L * R.d k)
    (P : ℕ → ℝ) (hP0 : P k₀ = 1) (hP : ∀ k, k₀ ≤ k → P (k + 1) = P k * a k)
    (Pbar : ℝ) (hPbar : Pbar = Real.exp (Cert.L * ∑' j, R.d (k₀ + j))) :
    ∀ k, k₀ ≤ k → 1 ≤ P k ∧ P k ≤ Pbar := by
  have hsum : Summable R.d :=
    R.summable_predicted_decreases_of_lower_bound Fstar fun k => hFstar.2 (Set.mem_range_self _)
  intro k hk
  rw [hPbar]
  exact BfgsCoverage.Article.Energy.normalization_bounds R Cert.L Cert.L_nonneg hsum k₀ P hP0
    (fun j hj => by rw [hP j hj, ha j]) k hk

/-- (S) at one accepted pair inside the band forces $C\ge0$: $0\le y_k^TW(x_{k+1})y_k\le Ct_k$
with $t_k>0$. So the constant $C_\eta$, allowed to be any real number in the theorem, is
nonnegative as soon as one accepted pair of the run lies in $K_\eta$ with $d_k\le\delta_\eta$. -/
theorem C_nonneg_of_pair {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η) (k : ℕ)
    (hxk : R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hxk1 : R.x (k + 1) ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) (hdk : R.d k ≤ Cert.δ) :
    0 ≤ Cert.C := by
  have hsmall : TransportedCertificate.pairDecrease (R.x k) (R.x (k + 1)) (R.g k) ≤ Cert.δ := by
    rwa [R.accepted_pair_decrease]
  have hS := Cert.secant _ _ _ _ hxk hxk1 (R.accepted_pair_eligible k) hsmall
  rw [R.accepted_pair_curvature] at hS
  have hpsd := Cert.positive_semidefinite _ hxk1 (R.hasGradient (k + 1)).differentiableAt
  have hnn : 0 ≤ metricEnergy (Cert.W (R.x (k + 1))) (R.g (k + 1) - R.g k) := by
    simpa only [metricEnergy, dot, dotProduct, star_trivial] using hpsd.2 (R.g (k + 1) - R.g k)
  have ht := R.curvature_pos k
  by_contra hneg
  push_neg at hneg
  have : Cert.C * R.curvature k < 0 := mul_neg_of_neg_of_pos hneg ht
  have hS' : metricEnergy (Cert.W (R.x (k + 1))) (R.g (k + 1) - R.g k) ≤
      Cert.C * R.curvature k := hS
  linarith

/-- Item `C/03_T/disp/021` (`companion/chapters/03_T.tex:161-164`): "Divide (6) by $P_{k+1}$ and
sum:
\[ \frac m{\overline P}\sum_{k=k_0}^{N-1}\frac1{q_k}\le E_{k_0}+C(N-k_0)." \]
Under the standing assumptions of displays `C/03_T/disp/018` and `C/03_T/disp/020`, for every
$N\ge k_0$. Here $C$ is the real constant of (S); it is nonnegative, because (S) applies to the
accepted pair $(x_{k_0},x_{k_0+1})$ (`C_nonneg_of_pair`). As for display `C/03_T/disp/019`, these
assumptions are jointly inconsistent; the proof uses the article's `certificate_budget_general`,
whose assumptions are satisfiable. ("Divide (6)" means (3.6), `trace_recurrence`, and "This
contradicts (5)" at line 165 means (3.5), `reciprocal_mean_diverges`: typos, recorded as item
`C/03_T/prose/042`.) -/
theorem reciprocal_budget {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ)
    (hFstar : IsLeast (Set.range F) Fstar) (b : ℝ) (K : Set (Vec n))
    (hK_def : K = {x | F x ≤ b}) (_hb : b > Fstar) (_hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (_hcert : TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂)
    (hx0 : R.x 0 ∈ K) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun k => F (R.x k) - Fstar) atTop (𝓝 ℓ))
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ (ℓ / 2))
    (k₀ : ℕ) (hk₀ : ∀ k, k₀ ≤ k → R.d k ≤ Cert.δ)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (Pbar : ℝ) (hPbar : Pbar = Real.exp (Cert.L * ∑' j, R.d (k₀ + j))) :
    ∀ N : ℕ, k₀ ≤ N →
      Cert.m / Pbar * ∑ k ∈ Finset.Ico k₀ N, (R.q k)⁻¹ ≤ E k₀ + Cert.C * ((N : ℝ) - k₀) := by
  intro N hN
  have hband := BfgsCoverage.Article.Energy.iterates_in_band b K hK_def Fstar R hx0 ℓ hℓ hlim
  have hC := C_nonneg_of_pair R K Fstar (ℓ / 2) Cert k₀ (hband k₀) (hband (k₀ + 1))
    (hk₀ k₀ le_rfl)
  have hsum : Summable R.d :=
    R.summable_predicted_decreases_of_lower_bound Fstar fun k => hFstar.2 (Set.mem_range_self _)
  exact BfgsCoverage.Article.Energy.certificate_budget_general R K Fstar (ℓ / 2) Cert hC hsum E hE
    k₀ N hN (fun k _ _ => hband k) (fun k hk _ => hk₀ k hk) Pbar hPbar

/-! ### The formal proof route (line 167) -/

/-- Item `C/03_T/prose/017` (`companion/chapters/03_T.tex:167-167`): "The formal principal theorem
uses the same derived trace recurrence with a harmless larger additive bound
$C_+(k+1)$, where $C_+=\max\{C,0\}$." For a certificate on a band $K_\eta$ and an index $k$ with
$x_k,x_{k+1}\in K_\eta$ and $d_k\le\delta$, the recurrence (3.6) implies
\[ E_{k+1}\le(1+Ld_k)(E_k-m/q_k)+C_+(k+1). \]
(The formal principal theorem is the library's `AdmissibleBFGSRun.band_certificate_incompatible`,
applied to a shifted run in `AdmissibleBFGSRun.transported_certificate_values`.) -/
theorem enlarged_recurrence {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace) (k : ℕ)
    (hxk : R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hxk1 : R.x (k + 1) ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) (hdk : R.d k ≤ Cert.δ) :
    E (k + 1) ≤
      (1 + Cert.L * R.d k) * (E k - Cert.m / R.q k) + max Cert.C 0 * ((k : ℝ) + 1) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Mat n,
      ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) := ⟨_, fun _ => rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := trace_step_general R K Fstar η Cert E hE
    (fun k => 1 + Cert.L * R.d k) (fun _ => rfl) M hM k hxk hxk1 hdk
  have hC : Cert.C ≤ max Cert.C 0 * ((k : ℝ) + 1) := by
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    calc Cert.C ≤ max Cert.C 0 := le_max_left _ _
      _ = max Cert.C 0 * 1 := (mul_one _).symm
      _ ≤ max Cert.C 0 * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_left hk (le_max_right _ _)
  linarith

/-- $\sum_{k<N}(k+1)=N(N+1)/2$. -/
theorem sum_range_succ_cast (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k : ℝ) + 1) = (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Chapter~M's Theorem `M:superquadratic` for an admissible run, in the form used at line 167:
with bounded gradients ($\|g_k\|^2\le G^2$) and $\sum_kd_k<\infty$,
$\frac1{N^2}\sum_{k<N}q_k^{-1}\to\infty$ (library `superquadraticReciprocalGrowth`). -/
theorem superquadratic_growth {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (G : ℝ)
    (hG : 0 < G) (hg : ∀ k, sqNorm (R.g k) ≤ G ^ 2) (hs : Summable R.d) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (R.q k)⁻¹) / (N : ℝ) ^ 2) atTop atTop :=
  superquadraticReciprocalGrowth n R.toFullBFGSRun G (1 - R.c₂) hG R.wolfe_constant_pos hg
    R.beta_lower_bound hs

/-- Item `C/03_T/prose/018` (`companion/chapters/03_T.tex:167-167`): "The normalized energy
estimate then gives an $O(N^2)$ reciprocal-sum bound and contradicts Chapter~M's
superquadratic theorem." If every iterate of a run lies in one band $K_\eta$ of a certificate
and $d_k\le\delta$ for all $k$, with $\sum_kd_k<\infty$, then for every $N$
\[ \frac{m}{\exp(\sum_kLd_k)}\sum_{k<N}\frac1{q_k}\le E_0+C_+\frac{N(N+1)}2, \]
an $O(N^2)$ bound; with bounded gradients this contradicts Theorem `M:superquadratic`
(`superquadratic_growth`): no such run exists. -/
theorem quadratic_budget {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (hband : ∀ k, R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) (hsmall : ∀ k, R.d k ≤ Cert.δ)
    (hs : Summable R.d) :
    (∀ N : ℕ, Cert.m / Real.exp (∑' k, Cert.L * R.d k) * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤
        E 0 + max Cert.C 0 * ((N : ℝ) * (N + 1) / 2)) ∧
      ((∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (R.g k) ≤ G ^ 2) → False) := by
  refine ⟨fun N => ?_, fun ⟨G, hG, hg⟩ =>
    R.band_certificate_incompatible Cert hband hsmall G hG hg hs⟩
  have h := ResidualBudget.residual_reciprocal_sum_le (E := E) (q := R.q)
    (u := fun k => Cert.L * R.d k) (m := Cert.m) (C := max Cert.C 0)
    (fun k => by rw [hE k]; exact R.certificateEnergy_nonneg Cert k (hband k)) R.q_pos
    (fun k => mul_nonneg Cert.L_nonneg (R.d_pos k).le) (hs.mul_left Cert.L) Cert.m_pos
    (le_max_right _ _)
    (fun k => enlarged_recurrence R K Fstar η Cert E hE k (hband k) (hband (k + 1)) (hsmall k)) N
  rwa [sum_range_succ_cast] at h

/-- Finite-horizon form of `quadratic_budget` (its hypotheses are satisfiable, see the examples
at the end): if $x_k\in K_\eta$ for $k\le N$, $d_k\le\delta$ for $k<N$ and $\sum_kd_k<\infty$, then
\[ \frac{m}{\exp(\sum_kLd_k)}\sum_{k<N}\frac1{q_k}\le E_0+C_+\frac{N(N+1)}2. \] -/
theorem quadratic_budget_finite {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace) (hs : Summable R.d)
    (N : ℕ) (hband : ∀ k, k ≤ N → R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η})
    (hsmall : ∀ k, k < N → R.d k ≤ Cert.δ) :
    Cert.m / Real.exp (∑' k, Cert.L * R.d k) * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤
      E 0 + max Cert.C 0 * ((N : ℝ) * (N + 1) / 2) := by
  have hE0 : 0 ≤ E 0 := by
    rw [hE 0]
    exact R.certificateEnergy_nonneg Cert 0 (hband 0 (Nat.zero_le N))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty, mul_zero, CharP.cast_eq_zero, zero_mul,
      zero_div, add_zero]
    exact hE0
  have hC := C_nonneg_of_pair R K Fstar η Cert 0 (hband 0 (Nat.zero_le N)) (hband 1 hN)
    (hsmall 0 hN)
  have h := BfgsCoverage.Article.Energy.certificate_budget_general R K Fstar η Cert hC hs E hE 0 N
    (Nat.zero_le N) (fun k _ hk => hband k hk) (fun k _ hk => hsmall k hk) _ rfl
  have hP : Real.exp (Cert.L * ∑' j, R.d (0 + j)) = Real.exp (∑' k, Cert.L * R.d k) := by
    simp only [zero_add, tsum_mul_left]
  rw [hP, ← Finset.range_eq_Ico] at h
  have hmax : max Cert.C 0 = Cert.C := max_eq_left hC
  have hNN : (N : ℝ) ≤ (N : ℝ) * (N + 1) / 2 := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  rw [hmax]
  have := mul_le_mul_of_nonneg_left hNN hC
  push_cast at h
  linarith

/-- Item `C/03_T/prose/019` (`companion/chapters/03_T.tex:167-167`): "Its additional
summability requirement is already a consequence of Armijo and the finite limiting value." If the
values $F(x_k)$ of an admissible run have a finite limit, then $\sum_kd_k<\infty$. -/
theorem summable_of_limit {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) (ℓ : ℝ)
    (hℓ : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ)) : Summable R.d :=
  R.summable_predicted_decreases_of_value_limit ℓ hℓ

/-- Item `C/03_T/prose/021` (`companion/chapters/03_T.tex:167-167`): "The sharper linear
telescoping estimate above follows from the separately proved scalar transport budget". If every
iterate lies in one band $K_\eta$ of a certificate, $d_k\le\delta$ for all $k$ and
$\sum_kd_k<\infty$, then for every $N$
\[ \frac{m}{\exp(\sum_kLd_k)}\sum_{k<N}\frac1{q_k}\le E_0+CN, \]
derived from the scalar budget `ScalarTransport.reciprocal_sum_le` (with $C\ge0$ from
`C_nonneg_of_pair`). -/
theorem linear_budget {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)
    (K : Set (Vec n)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η)
    (E : ℕ → ℝ) (hE : ∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace)
    (hband : ∀ k, R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) (hsmall : ∀ k, R.d k ≤ Cert.δ)
    (hs : Summable R.d) (N : ℕ) :
    Cert.m / Real.exp (∑' k, Cert.L * R.d k) * ∑ k ∈ Finset.range N, (R.q k)⁻¹ ≤
      E 0 + Cert.C * N := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Mat n,
      ∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k) := ⟨_, fun _ => rfl⟩
  have hC := C_nonneg_of_pair R K Fstar η Cert 0 (hband 0) (hband 1) (hsmall 0)
  exact ScalarTransport.reciprocal_sum_le (E := E) (q := R.q) (u := fun k => Cert.L * R.d k)
    (fun k => by rw [hE k]; exact R.certificateEnergy_nonneg Cert k (hband k)) R.q_pos
    (fun k => mul_nonneg Cert.L_nonneg (R.d_pos k).le) (hs.mul_left Cert.L) Cert.m_pos hC
    (fun k => by
      obtain ⟨h1, h2, h3, h4⟩ := trace_step_general R K Fstar η Cert E hE
        (fun k => 1 + Cert.L * R.d k) (fun _ => rfl) M hM k (hband k) (hband (k + 1)) (hsmall k)
      linarith) N

/-! ### Subsection "Local statement and weaker band requirements" (lines 173-180) -/

/-- Item `C/03_T/disp/022` (`companion/chapters/03_T.tex:175-177`): "If the assumptions hold
only in a neighborhood $U$ of a unique minimizer and $K$ is a compact low sublevel, choose an
initial level below $\inf_{x\in K\setminus U}F(x)>F_*$." For finite convex $F$ with unique
minimizer $x_*$ ($F_*=F(x_*)$), a compact sublevel $K$ and a neighborhood $U$ of $x_*$, there is
$c>F_*$ with $F(x)\ge c$ for every $x\in K\setminus U$; so the infimum exceeds $F_*$ (it is
$+\infty$ when $K\setminus U=\emptyset$). The constant is $F_*+\delta$ with
$\{F\le F_*+\delta\}\subseteq U$. -/
theorem outside_neighborhood_gap {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (b : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b}) (_hK : IsCompact K)
    (U : Set (Vec n)) (hU : U ∈ 𝓝 xstar) :
    ∃ c : ℝ, F xstar < c ∧ ∀ x ∈ K, x ∉ U → c ≤ F x := by
  obtain ⟨δ, hδ, hsub⟩ := Localization.neighborhood_basin hF xstar hmin huniq hU
  refine ⟨F xstar + δ, by linarith, fun x _ hxU => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hxU (hsub (show F x ≤ F xstar + δ from hlt.le))

/-- Item `C/03_T/prose/022` (`companion/chapters/03_T.tex:174-178`): "If the assumptions hold
only in a neighborhood $U$ of a unique minimizer and $K$ is a compact low sublevel, choose an
initial level below [display 022]. Armijo then traps all accepted iterates in $U$. This produces a
local basin independent of $H_0$." With certificates only on $K\cap U$ (for fixed constants
$c_1,c_2$), there is $\delta>0$, chosen before the run, such that every admissible run with
these constants and $F(x_0)\le F_*+\delta$ (any $H_0\succ0$) stays in $K\cap U$, and
$F(x_k)\to F_*$, $x_k\to x_*$. (Library: `local_transported_certificate_basin`.) -/
theorem local_basin {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar) (b : ℝ)
    (hb : F xstar < b) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b})
    (U : Set (Vec n)) (hU : U ∈ 𝓝 xstar) (c₁ c₂ : ℝ)
    (hcert : TransportedCertificate.HasBandCertificates F (K ∩ U) (F xstar) c₁ c₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, R.c₁ = c₁ → R.c₂ = c₂ →
      F (R.x 0) ≤ F xstar + δ →
        (∀ k, R.x k ∈ K ∧ R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto R.x atTop (𝓝 xstar) := by
  subst hK_def
  obtain ⟨δ, hδ, h⟩ := TransportedCertificate.local_transported_certificate_basin hF xstar hmin
    huniq b hb hU hcert
  exact ⟨δ, hδ, fun R h1 h2 h0 => h R h1 h2 h0⟩

/-- Item `C/03_T/prose/023` (`companion/chapters/03_T.tex:178-178`): "Rejected trial points need
not stay in $U$." Example: $F(x)=x^2/2$ on $\R$ with minimizer $0$, the neighborhood
$U=\{|x|<1\}$, the start $x_0=1/2\in U$ (with $F(x_0)=1/8$) and $H_0=4$: the unit trial point
$x_0-H_0\nabla F(x_0)=-3/2$ lies outside $U$ and violates Armijo for every $0<c_1<1$, so it is
rejected, while the accepted point $x_0-\tfrac18H_0\nabla F(x_0)=1/4$ ($\alpha=1/8$) satisfies
Armijo for $c_1\le3/4$ and lies in $U$. -/
theorem rejected_trial_outside :
    ∃ (F : Vec 1 → ℝ) (U : Set (Vec 1)) (x₀ g₀ : Vec 1) (H₀ : Mat 1),
      (∀ x, F x = x 0 ^ 2 / 2) ∧ ConvexOn ℝ Set.univ F ∧ (∀ x, F 0 ≤ F x) ∧
      U ∈ 𝓝 (0 : Vec 1) ∧ x₀ ∈ U ∧ H₀.PosDef ∧ HasFDerivAt F (gradientFunctional g₀) x₀ ∧
      x₀ + bfgsStep H₀ g₀ 1 ∉ U ∧
      (∀ c₁ : ℝ, 0 < c₁ → c₁ < 1 →
        ¬ F (x₀ + bfgsStep H₀ g₀ 1) ≤ F x₀ + c₁ * dot g₀ (bfgsStep H₀ g₀ 1)) ∧
      x₀ + bfgsStep H₀ g₀ (1 / 8) ∈ U ∧
      (∀ c₁ : ℝ, c₁ ≤ 3 / 4 →
        F (x₀ + bfgsStep H₀ g₀ (1 / 8)) ≤ F x₀ + c₁ * dot g₀ (bfgsStep H₀ g₀ (1 / 8))) := by
  have hU : {x : Vec 1 | |x 0| < 1} ∈ 𝓝 (0 : Vec 1) := by
    have ho : IsOpen {x : Vec 1 | |x 0| < 1} :=
      isOpen_lt (continuous_abs.comp (continuous_apply 0)) continuous_const
    exact ho.mem_nhds (by simp)
  refine ⟨BfgsCoverage.Article.Energy.Example.quad, {x | |x 0| < 1}, fun _ => 1 / 2,
    fun _ => 1 / 2, Matrix.diagonal (fun _ => 4), fun _ => rfl,
    BfgsCoverage.Article.Energy.Example.quad_convex, ?_, hU, ?_, ?_,
    BfgsCoverage.Article.Energy.Example.quad_hasGradient _, ?_, ?_, ?_, ?_⟩
  · intro x
    have h0 : BfgsCoverage.Article.Energy.Example.quad 0 = 0 := by
      simp [BfgsCoverage.Article.Energy.Example.quad]
    rw [h0]
    exact BfgsCoverage.Article.Energy.Example.quad_nonneg x
  · show |(1 / 2 : ℝ)| < 1
    rw [abs_of_pos (by norm_num)]
    norm_num
  · exact Matrix.PosDef.diagonal (fun _ => by norm_num)
  · show ¬ |(fun _ => (1 / 2 : ℝ)) 0 + bfgsStep (Matrix.diagonal fun _ => (4 : ℝ))
      (fun _ => 1 / 2) 1 0| < 1
    simp [bfgsStep, Matrix.mulVec_diagonal]
    norm_num [abs_of_neg]
  · intro c₁ hc₁ _
    simp [BfgsCoverage.Article.Energy.Example.quad, bfgsStep, Matrix.mulVec_diagonal, dot]
    nlinarith
  · show |(fun _ => (1 / 2 : ℝ)) 0 + bfgsStep (Matrix.diagonal fun _ => (4 : ℝ))
      (fun _ => 1 / 2) (1 / 8) 0| < 1
    simp [bfgsStep, Matrix.mulVec_diagonal]
    norm_num
    rw [abs_of_pos (by norm_num)]
    norm_num
  · intro c₁ hc₁
    simp [BfgsCoverage.Article.Energy.Example.quad, bfgsStep, Matrix.mulVec_diagonal, dot]
    nlinarith

/-- Item `C/03_T/prose/024` (`companion/chapters/03_T.tex:178-178`): "For multiple minimizers,
one may instead use a neighborhood of the entire compact solution set or directly assume that the
initial sublevel lies in the structural region." (a) With a neighborhood $U$ of every minimizer
and certificates on $\{F\le b\}\cap U$ ($\{F\le b\}$ compact, $b>F_*$), there is $\delta>0$ such
that every admissible run with the fixed constants and $F(x_0)\le F_*+\delta$ stays in
$\{F\le b\}\cap U$, $F(x_k)\to F_*$ and $\operatorname{dist}(x_k,\arg\min F)\to0$ (library
`local_transported_certificate_basin_of_compact_solution_set`). (b) If certificates hold on a
structural region $S$ and the compact initial sublevel $\{F\le F(x_0)\}$ lies in $S$, the run
converges in value and in distance to $\arg\min F$. -/
theorem solution_set_basin {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (hb : F xstar < b) (hK : IsCompact {x | F x ≤ b})
    (U : Set (Vec n)) (hU : ∀ x, F x = F xstar → U ∈ 𝓝 x) (c₁ c₂ : ℝ)
    (hcert : TransportedCertificate.HasBandCertificates F ({x | F x ≤ b} ∩ U) (F xstar) c₁ c₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, R.c₁ = c₁ → R.c₂ = c₂ →
      F (R.x 0) ≤ F xstar + δ →
        (∀ k, F (R.x k) ≤ b ∧ R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
          Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, h⟩ :=
    TransportedCertificate.local_transported_certificate_basin_of_compact_solution_set hF xstar
      hmin b hb hK hU hcert
  exact ⟨δ, hδ, fun R h1 h2 h0 => ⟨(h R h1 h2 h0).1, (h R h1 h2 h0).2.1, (h R h1 h2 h0).2.2.1⟩⟩

/-- Item `C/03_T/prose/024` (`companion/chapters/03_T.tex:178-178`), part (b): certificates on a
structural region $S$ containing the compact initial sublevel $\{F\le F(x_0)\}$ give
$F(x_k)\to F_*$ and $\operatorname{dist}(x_k,\arg\min F)\to0$, and $x_k\to x_*$ when the minimizer
$x_*$ is unique. -/
theorem structural_region_convergence {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (S : Set (Vec n)) (R : AdmissibleBFGSRun n F)
    (hcert : TransportedCertificate.HasBandCertificates F S (F xstar) R.c₁ R.c₂)
    (hK : IsCompact {x | F x ≤ F (R.x 0)}) (hKS : {x | F x ≤ F (R.x 0)} ⊆ S) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F xstar → x = xstar) → Tendsto R.x atTop (𝓝 xstar)) :=
  transportedCertificateConvergence R (F (R.x 0)) hK xstar hmin le_rfl
    (TransportedCertificate.hasBandCertificates_restrict hcert hKS)

/-- The positive band of $K\cap\{F\le\ell+\varepsilon\}$ at level $\eta=\ell-F_*$ is the shell
$\{x\in K:\ell\le F(x)\le\ell+\varepsilon\}$. -/
theorem shell_band_eq {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (Fstar ℓ ε : ℝ) :
    {x | x ∈ K ∩ {x | F x ≤ ℓ + ε} ∧ F x ≥ Fstar + (ℓ - Fstar)} =
      {x | x ∈ K ∧ ℓ ≤ F x ∧ F x ≤ ℓ + ε} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, add_sub_cancel]
  tauto

/-- Item `C/03_T/prose/025` (`companion/chapters/03_T.tex:180-180`): "The proof only needs a
certificate in a small one-sided level neighborhood of each possible finite limit $\ell>F_*$.
Requiring a field on every whole positive band is a cleaner, stronger formulation; certificates
on shells $\ell\le F\le\ell+\epsilon_\ell$ also suffice." (a) Band certificates give shell
certificates (`HasShellCertificates`: for every $\ell>F_*$ such that some $x\in K$ has
$F(x)\ge\ell$, some $\varepsilon_\ell>0$ and a certificate on $K\cap\{F\le\ell+\varepsilon_\ell\}$
at level $\eta=\ell-F_*$, whose band is the shell, `shell_band_eq`). (b) Shell certificates
suffice: every admissible run starting in the compact $K=\{F\le b\}$ satisfies $F(x_k)\to F_*$,
$\operatorname{dist}(x_k,\arg\min F)\to0$, and $x_k\to x_*$ for a unique minimizer. -/
theorem shell_certificates {n : ℕ} {F : Vec n → ℝ} (Fstar : ℝ) (K : Set (Vec n)) (c₁ c₂ : ℝ) :
    TransportedCertificate.HasBandCertificates F K Fstar c₁ c₂ →
      TransportedCertificate.HasShellCertificates F K Fstar c₁ c₂ := by
  intro h ℓ hℓ ⟨x, hxK, hxℓ⟩
  obtain ⟨Cert⟩ := h (ℓ - Fstar) (by linarith) ⟨x, hxK, by linarith⟩
  exact ⟨1, one_pos, ⟨Cert.restrict _ Set.inter_subset_left⟩⟩

/-- Item `C/03_T/prose/025` (`companion/chapters/03_T.tex:180-180`), part (b): shell
certificates suffice for the conclusions of the theorem. -/
theorem shell_convergence {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (b : ℝ) (K : Set (Vec n)) (hK_def : K = {x | F x ≤ b}) (hK : IsCompact K)
    (R : AdmissibleBFGSRun n F)
    (hcert : TransportedCertificate.HasShellCertificates F K (F xstar) R.c₁ R.c₂)
    (hx0 : R.x 0 ∈ K) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
      Tendsto (fun k => euclideanSolutionDistance F (R.x k)) atTop (𝓝 0) ∧
      ((∀ x, F x = F xstar → x = xstar) → Tendsto R.x atTop (𝓝 xstar)) := by
  subst hK_def
  obtain ⟨hv, -, hu⟩ :=
    R.transported_shell_certificate_convergence_on_sublevel b hK xstar hmin hx0 hcert
  exact ⟨hv, euclidean_distance_to_argmin_of_values (convex_continuous R.convex) xstar hmin hK
    (fun k => (R.objective_le_initial k).trans hx0) hv, hu⟩

/-! ### Subsection "Scalar form and freedom to rescale" (lines 186-202) -/

/-- Item `C/03_T/disp/023` (`companion/chapters/03_T.tex:188-191`): "Taking $W(x)=v(x)v(x)^T$, a
sufficient version of (T) is $v(z)=\lambda(x,z)v(x)+\beta(x,z)s$, $|\lambda(x,z)|^2\le1+Ld$."
For all vectors $v(x),v(z),s$ and reals $\lambda,\beta,L,d$: if $v(z)=\lambda v(x)+\beta s$ and
$|\lambda|^2\le1+Ld$, then
$\Pi_s\,v(z)v(z)^T\,\Pi_s\preceq(1+Ld)\,\Pi_s\,v(x)v(x)^T\,\Pi_s$, which is
(T) for the field $W=vv^T$. Nothing else is asked of $\lambda$ (library `rank_one_transport`). -/
theorem rank_one_sufficient {n : ℕ} (vx vz s : Vec n) (lam β L d : ℝ)
    (hv : vz = lam • vx + β • s) (hlam : |lam| ^ 2 ≤ 1 + L * d) :
    ((1 + L * d) • (TransportedCertificate.stepProjector s * outer vx vx *
        TransportedCertificate.stepProjector s) -
      TransportedCertificate.stepProjector s * outer vz vz *
        TransportedCertificate.stepProjector s).PosSemidef :=
  TransportedCertificate.rank_one_transport s vx vz lam β (1 + L * d) hv (by rwa [sq_abs] at hlam)

/-- Item `C/03_T/disp/024` (`companion/chapters/03_T.tex:193-195`): "Conditions (V)--(S) become
$|g^Tv(x)|^2\ge m$, $|y^Tv(z)|^2\le Ct$." For $W=vv^T$: $g^TWg=|g^Tv|^2$ and $y^TWy=|y^Tv|^2$, so
(V) and (S) for $W(x)=v(x)v(x)^T$ read as displayed (`rank_one_certificate` assembles the band
certificate from these scalar conditions and the transport of display `C/03_T/disp/023`). -/
theorem rank_one_conditions {n : ℕ} (v g y : Vec n) :
    dot g (outer v v *ᵥ g) = |dot g v| ^ 2 ∧ dot y (outer v v *ᵥ y) = |dot y v| ^ 2 := by
  refine ⟨?_, ?_⟩
  · rw [sq_abs, dot_comm' g v]
    exact EnergyIdentities.energy_outer v g
  · rw [sq_abs, dot_comm' y v]
    exact EnergyIdentities.energy_outer v y

/-- The scalar form assembled (lines 187-195): a vector field $v$ with $|g^Tv(x)|^2\ge m$ on the
band, $|y^Tv(z)|^2\le Ct$ and $v(z)=\lambda v(x)+\beta s$, $|\lambda|^2\le1+Ld$ on eligible pairs in
the band with $d\le\delta$, gives a band certificate with field $W=vv^T$ and the same constants
(library `rankOneCertificate`). -/
theorem rank_one_certificate {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ}
    (v : Vec n → Vec n) (m C L δ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hV : ∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ g : Vec n,
      HasFDerivAt F (gradientFunctional g) x → |dot g (v x)| ^ 2 ≥ m)
    (hS : ∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
      ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
        -dot g (z - x) ≤ δ → |dot (h - g) (v z)| ^ 2 ≤ C * dot (h - g) (z - x))
    (hT : ∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
      ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
        -dot g (z - x) ≤ δ →
        ∃ lam β : ℝ, v z = lam • v x + β • (z - x) ∧ |lam| ^ 2 ≤ 1 + L * -dot g (z - x)) :
    ∃ Cert : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η,
      Cert.W = (fun x => outer (v x) (v x)) ∧ Cert.m = m ∧ Cert.C = C ∧ Cert.L = L ∧
        Cert.δ = δ :=
  ⟨TransportedCertificate.rankOneCertificate v m C L δ hm hL hδ
    (fun x hx g hg => by
      have h := hV x hx g hg
      rwa [sq_abs] at h)
    (fun x z g h hx hz hp hd => by
      have h' := hS x hx z hz g h hp hd
      rwa [sq_abs] at h')
    (fun x z g h hx hz hp hd => by
      obtain ⟨lam, β, h1, h2⟩ := hT x hx z hz g h hp hd
      exact ⟨lam, β, h1, by rwa [sq_abs] at h2⟩), rfl, rfl, rfl, rfl, rfl⟩

/-- Item `C/03_T/prose/026` (`companion/chapters/03_T.tex:196-196`): "there is no requirement that
$\lambda$ be invertible or bounded away from zero." The sufficient condition of display
`C/03_T/disp/023` asks only $|\lambda|^2\le1+Ld$, and the degenerate multiplier $\lambda=0$ is
allowed: if $v(z)=\beta s$, then (T) holds for $W=vv^T$ with every $L,d$ such that $1+Ld\ge0$.
(The sentence opens with a contrast, "Unlike the preceding moving-frame theorem", recorded as the
discrepancy item `C/03_T/prose/043`: the moving-frame criterion of Chapter~M, `02_M.tex:196-211`,
assumes bounded inverse norms of the cumulative transports; Theorem `M:residualtheorem` does
not.) -/
theorem rank_one_degenerate {n : ℕ} (vx vz s : Vec n) (β L d : ℝ) (hv : vz = β • s)
    (hLd : 0 ≤ 1 + L * d) :
    ((1 + L * d) • (TransportedCertificate.stepProjector s * outer vx vx *
        TransportedCertificate.stepProjector s) -
      TransportedCertificate.stepProjector s * outer vz vz *
        TransportedCertificate.stepProjector s).PosSemidef :=
  rank_one_sufficient vx vz s 0 β L d (by rw [hv, zero_smul, zero_add]) (by simpa using hLd)

/-- Item `C/03_T/prose/026` (`companion/chapters/03_T.tex:196-196`), an instance where the
multiplier must vanish: in $\R^2$, with $v(x)=e_1$, $s=e_2$ and $v(z)=e_2$, every decomposition
$v(z)=\lambda v(x)+\beta s$ has $\lambda=0$ (one exists, with $\beta=1$), and (T) holds for $W=vv^T$
with $L=0$ and every $d$. -/
theorem degenerate_multiplier :
    (∀ lam β : ℝ, (![0, 1] : Vec 2) = lam • ![1, 0] + β • ![0, 1] → lam = 0) ∧
      (![0, 1] : Vec 2) = (0 : ℝ) • ![1, 0] + (1 : ℝ) • ![0, 1] ∧
      ∀ d : ℝ, ((1 + 0 * d) • (TransportedCertificate.stepProjector ![0, 1] *
          outer ![1, 0] ![1, 0] * TransportedCertificate.stepProjector ![0, 1]) -
        TransportedCertificate.stepProjector ![0, 1] * outer ![0, 1] ![0, 1] *
          TransportedCertificate.stepProjector ![0, 1]).PosSemidef := by
  refine ⟨fun lam β h => ?_, ?_, fun d => ?_⟩
  · have h0 := congrFun h 0
    simp at h0
    linarith
  · ext i
    fin_cases i <;> simp
  · exact rank_one_degenerate ![1, 0] ![0, 1] ![0, 1] 1 0 d (by rw [one_smul]) (by simp)

/-- Item `C/03_T/prose/027` (`companion/chapters/03_T.tex:196-196`): "The PSD form also
accommodates multiple comparison directions and varying rank, without choosing an exact frame
transport." The sum of two certificates on the same band (for instance of two rank-one fields, or
of fields of different ranks) is again a certificate, with $m=m_1+m_2$, $C=C_1+C_2$,
$L=\max\{L_1,L_2\}$, $\delta=\min\{\delta_1,\delta_2\}$; transport is only the Loewner inequality
(T), no exact relation between frames at $x$ and $z$. The definition imposes no rank condition. -/
theorem certificate_sum {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ}
    (C1 C2 : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η) :
    ∃ Cert : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η,
      Cert.W = (fun x => C1.W x + C2.W x) ∧ Cert.m = C1.m + C2.m ∧ Cert.C = C1.C + C2.C ∧
        Cert.L = max C1.L C2.L ∧ Cert.δ = min C1.δ C2.δ := by
  refine ⟨{ W := fun x => C1.W x + C2.W x, m := C1.m + C2.m, C := C1.C + C2.C,
            L := max C1.L C2.L, δ := min C1.δ C2.δ, m_pos := add_pos C1.m_pos C2.m_pos,
            L_nonneg := le_max_of_le_left C1.L_nonneg,
            delta_pos := lt_min C1.delta_pos C2.delta_pos,
            positive_semidefinite := fun x hx hd =>
              (C1.positive_semidefinite x hx hd).add (C2.positive_semidefinite x hx hd),
            visibility := fun x hx g hg => ?_, secant := fun x z g h hx hz hp hd => ?_,
            transport := fun x z g h hx hz hp hd => ?_ }, rfl, rfl, rfl, rfl, rfl⟩
  · rw [EnergyIdentities.energy_add_matrix]
    linarith [C1.visibility x hx g hg, C2.visibility x hx g hg]
  · rw [EnergyIdentities.energy_add_matrix]
    have h1 := C1.secant x z g h hx hz hp (hd.trans (min_le_left _ _))
    have h2 := C2.secant x z g h hx hz hp (hd.trans (min_le_right _ _))
    linarith
  · have hdpos := hp.decrease_pos
    have hX1 := TransportedCertificate.projected_psd
      (C1.positive_semidefinite x hx hp.gradient_x.differentiableAt)
      (TransportedCertificate.pairStep x z)
    have hX2 := TransportedCertificate.projected_psd
      (C2.positive_semidefinite x hx hp.gradient_x.differentiableAt)
      (TransportedCertificate.pairStep x z)
    have hT1 := TransportedCertificate.scale_loewner hX1 zero_le_one
      (C1.transport x z g h hx hz hp (hd.trans (min_le_left _ _)))
      (v := 1 + max C1.L C2.L * TransportedCertificate.pairDecrease x z g) (by
        have := mul_le_mul_of_nonneg_right (le_max_left C1.L C2.L) hdpos.le
        linarith)
    have hT2 := TransportedCertificate.scale_loewner hX2 zero_le_one
      (C2.transport x z g h hx hz hp (hd.trans (min_le_right _ _)))
      (v := 1 + max C1.L C2.L * TransportedCertificate.pairDecrease x z g) (by
        have := mul_le_mul_of_nonneg_right (le_max_right C1.L C2.L) hdpos.le
        linarith)
    convert hT1.add hT2 using 1
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, one_smul]
    abel

/-- Item `C/03_T/prose/028` (`companion/chapters/03_T.tex:198-202`), with its display
`C/03_T/disp/025`: "A bounded potential may be absorbed into $W$. If (T) instead has multiplier
$\exp\{Ld+\Psi(x)-\Psi(z)\}$, where $\Psi$ is bounded on the band, replace $W$ by $e^\Psi W$. This
gives multiplier $e^{Ld}$, which is at most $1+L'd$ for $d$ sufficiently small. The other bounds
change only by band-dependent constants." The hypothesis is the library's
`PotentialBandCertificate` (a field $W$ with (V), (S) and the PSD condition as in the theorem, a
potential $\Psi$ with $\psi_{lo}\le\Psi\le\psi_{hi}$ on the band, and (T) with the displayed
multiplier). Then: (T) holds for $e^\Psi W$ with multiplier exactly $e^{Ld}$;
$e^{Ld}\le1+2Ld$ for $0\le d\le1/(L+1)$; and $e^\Psi W$ is a band certificate with $L'=2L$,
$\delta'=\min\{\delta,1/(L+1)\}$, $m'=e^{\psi_{lo}}m$, $C'=e^{\psi_{hi}}\max\{C,0\}$. -/
theorem potential_absorption {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ}
    (hc₂ : c₂ < 1) (P : TransportedCertificate.PotentialBandCertificate F K Fstar c₁ c₂ η) :
    (∀ x ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}, ∀ z ∈ {x | x ∈ K ∧ F x ≥ Fstar + η},
      ∀ g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
        -dot g (z - x) ≤ P.δ →
        (Real.exp (P.L * -dot g (z - x)) •
            (TransportedCertificate.stepProjector (z - x) * (Real.exp (P.Ψ x) • P.W x) *
              TransportedCertificate.stepProjector (z - x)) -
          TransportedCertificate.stepProjector (z - x) * (Real.exp (P.Ψ z) • P.W z) *
            TransportedCertificate.stepProjector (z - x)).PosSemidef) ∧
      (∀ d : ℝ, 0 ≤ d → d ≤ (P.L + 1)⁻¹ → Real.exp (P.L * d) ≤ 1 + 2 * P.L * d) ∧
      ∃ Cert : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η,
        (∀ x, Cert.W x = Real.exp (P.Ψ x) • P.W x) ∧ Cert.m = Real.exp P.ψlo * P.m ∧
          Cert.C = Real.exp P.ψhi * max P.C 0 ∧ Cert.L = 2 * P.L ∧
          Cert.δ = min P.δ (P.L + 1)⁻¹ := by
  refine ⟨fun x hx z hz g h hp hd => ?_, fun d hd hsmall => ?_,
    ⟨P.absorb hc₂, P.absorb_field hc₂, rfl, rfl, (P.absorb_constants hc₂).1,
      (P.absorb_constants hc₂).2⟩⟩
  · have hX := TransportedCertificate.projected_psd
      (P.positive_semidefinite x hx hp.gradient_x.differentiableAt) (z - x)
    have hT := TransportedCertificate.scale_loewner hX (Real.exp_pos (P.Ψ z)).le
      (P.transport x z g h hx hz hp hd)
      (v := Real.exp (P.L * -dot g (z - x)) * Real.exp (P.Ψ x)) (by
        rw [← Real.exp_add, ← Real.exp_add]
        apply le_of_eq
        congr 1
        change P.Ψ z + (P.L * -dot g (z - x) + P.Ψ x - P.Ψ z) = _
        ring)
    simpa only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] using hT
  · have h := TransportedCertificate.exp_small_linear P.L_nonneg hd hsmall
    linarith

/-! ### Section "Why this is genuinely weaker than RS" (lines 216-239) -/

/-- The radial secant condition (RS) of Chapter~R (`companion/chapters/04_R.tex:53-59`, with
$C_\eta<\infty$) is the library's `HasRadialSecantBounds F K x_*`, literally: for every $\eta>0$
there is $C$ with $N^2\le CT$ whenever $x,z\in K$ are differentiable with gradients $g,h$,
$F_*+\eta\le F(z)\le F(x)$ and $T>0$, where $T=(h-g)^T(z-x)$, $N=(h-g)^T(z-x_*)$. -/
theorem rs_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (xstar : Vec n) :
    RadialCertificate.HasRadialSecantBounds F K xstar ↔
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x z g h : Vec n, x ∈ K → z ∈ K → F xstar + η ≤ F z →
        F z ≤ F x → HasFDerivAt F (gradientFunctional g) x →
        HasFDerivAt F (gradientFunctional h) z → 0 < dot (h - g) (z - x) →
        (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x) := Iff.rfl

/-- Item `C/03_T/disp/026` (`companion/chapters/03_T.tex:218-220`): "Given (RS), take
$W(x)=(x-x_*)(x-x_*)^T$." The field is `outer (x - xstar) (x - xstar)`, and its quadratic form is
$a^TW(x)a=(a^T(x-x_*))^2$. -/
theorem radial_field_energy {n : ℕ} (xstar x a : Vec n) :
    dot a (outer (x - xstar) (x - xstar) *ᵥ a) = (dot a (x - xstar)) ^ 2 := by
  rw [dot_comm' a (x - xstar)]
  exact EnergyIdentities.energy_outer (x - xstar) a

/-- Item `C/03_T/disp/027` (`companion/chapters/03_T.tex:222-224`): "Convexity gives
$g^TW(x)g=(g^T(x-x_*))^2\ge(F(x)-F_*)^2\ge\eta^2$." In the setting of the section ($F$ finite
convex with minimizer $x_*$, $F_*=F(x_*)$, compact $K=\{F\le b\}$, (RS)), for every differentiable
$x\in K_\eta$ with $g=\nabla F(x)$. -/
theorem radial_visibility {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (b : ℝ) (K : Set (Vec n)) (_hK_def : K = {x | F x ≤ b})
    (_hK : IsCompact K) (_hRS : RadialCertificate.HasRadialSecantBounds F K xstar)
    (η : ℝ) (hη : 0 < η) (x g : Vec n) (hx : x ∈ {x | x ∈ K ∧ F x ≥ F xstar + η})
    (hg : HasFDerivAt F (gradientFunctional g) x) :
    dot g (outer (x - xstar) (x - xstar) *ᵥ g) = (dot g (x - xstar)) ^ 2 ∧
      (dot g (x - xstar)) ^ 2 ≥ (F x - F xstar) ^ 2 ∧ (F x - F xstar) ^ 2 ≥ η ^ 2 := by
  have hs := convex_supporting_inequality hF hg xstar
  have he : dot g (xstar - x) = -dot g (x - xstar) := by
    unfold dot
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have h1 : F x - F xstar ≤ dot g (x - xstar) := by linarith
  have h0 : 0 ≤ F x - F xstar := by linarith [hmin x]
  have hb : η ≤ F x - F xstar := by have := hx.2; linarith
  refine ⟨radial_field_energy xstar x g, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- Item `C/03_T/prose/029` (`companion/chapters/03_T.tex:225-225`): "Condition (S) is exactly
(RS)", a discrepancy (imprecision); this is what holds. For $W(z)=(z-x_*)(z-x_*)^T$ the left side of
(S) is $y^TW(z)y=N^2$ with $N=(h-g)^T(z-x_*)$, and $t=T$; and every eligible pair $x,z\in K_\eta$
(for $0<c_1$, $c_2<1$) satisfies the premises of (RS): $x,z\in K$, $F_*+\eta\le F(z)\le F(x)$,
$T>0$. So, with this $W$, (S) is the inequality of (RS) restricted to eligible pairs in $K_\eta$
with $d\le\delta_\eta$, and (RS) gives (S) with the same constant (`rs_gives_s`); (S) does not give
(RS) (`s_not_exactly_rs`). -/
theorem radial_secant_exact {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (K : Set (Vec n))
    (c₁ c₂ η : ℝ) (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (x z g h : Vec n)
    (hx : x ∈ {x | x ∈ K ∧ F x ≥ F xstar + η}) (hz : z ∈ {x | x ∈ K ∧ F x ≥ F xstar + η})
    (hp : TransportedCertificate.EligiblePair F c₁ c₂ x z g h) :
    dot (h - g) (outer (z - xstar) (z - xstar) *ᵥ (h - g)) = (dot (h - g) (z - xstar)) ^ 2 ∧
      x ∈ K ∧ z ∈ K ∧ F xstar + η ≤ F z ∧ F z ≤ F x ∧ 0 < dot (h - g) (z - x) := by
  have hdec : F z ≤ F x := by
    have hp' := mul_pos hc₁ hp.decrease_pos
    linarith [hp.armijo]
  exact ⟨radial_field_energy xstar z (h - g), hx.1, hz.1, hz.2, hdec,
    TransportedCertificate.eligible_curvature_pos hp hc₂⟩

/-- Item `C/03_T/prose/029` (`companion/chapters/03_T.tex:225-225`), the implication that holds:
(RS) gives (S) with the same constant. If the (RS) inequality $N^2\le CT$ holds at the level
$\eta$ (for all differentiable $x,z\in K$ with $F_*+\eta\le F(z)\le F(x)$ and $T>0$), then the
radial field $W(z)=(z-x_*)(z-x_*)^T$ satisfies (S), $y^TW(z)y\le Ct$, with the same $C$ on every
eligible pair $x,z\in K_\eta$ (for $0<c_1$, $c_2<1$), whatever $d$. -/
theorem rs_gives_s {n : ℕ} {F : Vec n → ℝ} (xstar : Vec n) (K : Set (Vec n))
    (c₁ c₂ η C : ℝ) (hc₁ : 0 < c₁) (hc₂ : c₂ < 1)
    (hRS : ∀ x z g h : Vec n, x ∈ K → z ∈ K → F xstar + η ≤ F z → F z ≤ F x →
      HasFDerivAt F (gradientFunctional g) x → HasFDerivAt F (gradientFunctional h) z →
      0 < dot (h - g) (z - x) → (dot (h - g) (z - xstar)) ^ 2 ≤ C * dot (h - g) (z - x))
    (x z g h : Vec n)
    (hx : x ∈ {x | x ∈ K ∧ F x ≥ F xstar + η}) (hz : z ∈ {x | x ∈ K ∧ F x ≥ F xstar + η})
    (hp : TransportedCertificate.EligiblePair F c₁ c₂ x z g h) :
    dot (h - g) (outer (z - xstar) (z - xstar) *ᵥ (h - g)) ≤ C * dot (h - g) (z - x) := by
  obtain ⟨hW, hxK, hzK, hFz, hzx, ht⟩ :=
    radial_secant_exact xstar K c₁ c₂ η hc₁ hc₂ x z g h hx hz hp
  rw [hW]
  exact hRS x z g h hxK hzK hFz hzx hp.gradient_x hp.gradient_z ht

/-! #### The witness for item `C/03_T/prose/029`

$F(x)=\max\{|x|,2x-1\}$ on $\R$ (kinks at the minimizer $0$ and at $1$), $x_*=0$, $K=\{F\le2\}$:
(S) holds for the radial field, (RS) fails. Adapted from the witness of the independent review. -/

namespace Kink

/-- $F(x)=\max\{-x,x,2x-1\}=\max\{|x|,2x-1\}$. -/
def objective (x : Vec 1) : ℝ := max (max (-(x 0)) (x 0)) (2 * x 0 - 1)

/-- The point $c$ of $\R^1$. -/
def point (c : ℝ) : Vec 1 := fun _ => c

theorem dot_point (c : ℝ) (v : Vec 1) : dot (point c) v = c * v 0 := by
  simp [dot, point, Fin.sum_univ_one]

theorem objective_eq_abs (x : Vec 1) : objective x = max |x 0| (2 * x 0 - 1) := by
  unfold objective
  rw [abs_eq_max_neg, max_comm (x 0)]

theorem neg_le (z : Vec 1) : -(z 0) ≤ objective z :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem self_le (z : Vec 1) : z 0 ≤ objective z :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem line_le (z : Vec 1) : 2 * z 0 - 1 ≤ objective z := le_max_right _ _

theorem objective_of_nonpos {x : Vec 1} (h : x 0 ≤ 0) : objective x = -(x 0) := by
  unfold objective
  rw [max_eq_left (by linarith : x 0 ≤ -(x 0)), max_eq_left (by linarith : 2 * x 0 - 1 ≤ -(x 0))]

theorem objective_of_mid {x : Vec 1} (h0 : 0 ≤ x 0) (h1 : x 0 ≤ 1) : objective x = x 0 := by
  unfold objective
  rw [max_eq_right (by linarith : -(x 0) ≤ x 0), max_eq_left (by linarith : 2 * x 0 - 1 ≤ x 0)]

theorem objective_of_one_le {x : Vec 1} (h : 1 ≤ x 0) : objective x = 2 * x 0 - 1 := by
  unfold objective
  rw [max_eq_right (by linarith : -(x 0) ≤ x 0), max_eq_right (by linarith : x 0 ≤ 2 * x 0 - 1)]

theorem objective_convex : ConvexOn ℝ Set.univ objective := by
  have h1 : ConvexOn ℝ Set.univ (fun x : Vec 1 => -(x 0)) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have h2 : ConvexOn ℝ Set.univ (fun x : Vec 1 => x 0) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
    simp
  have h3 : ConvexOn ℝ Set.univ (fun x : Vec 1 => 2 * x 0 - 1) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb : b = 1 - a := by linarith
    subst hb
    nlinarith
  exact (h1.sup h2).sup h3

theorem objective_zero : objective 0 = 0 := by
  rw [objective_of_nonpos (by simp)]
  simp

theorem objective_min (x : Vec 1) : objective 0 ≤ objective x := by
  rw [objective_zero]
  have h1 := neg_le x
  have h2 := self_le x
  linarith

theorem objective_unique (x : Vec 1) (hx : objective x = objective 0) : x = 0 := by
  rw [objective_zero] at hx
  have h1 := neg_le x
  have h2 := self_le x
  funext i
  fin_cases i
  show x 0 = 0
  linarith

/-- At a point of differentiability the gradient is $-1$ left of $0$, $1$ on $(0,1)$ and $2$
right of $1$; $F$ is not differentiable at $0$ and $1$. -/
theorem gradient_cases {x g : Vec 1} (hg : HasFDerivAt objective (gradientFunctional g) x) :
    (x 0 < 0 ∧ g = point (-1)) ∨ (0 < x 0 ∧ x 0 < 1 ∧ g = point 1) ∨
      (1 < x 0 ∧ g = point 2) := by
  have sneg : x 0 ≤ 0 → ∀ z, dot (point (-1)) (z - x) ≤ objective z - objective x := by
    intro h z
    rw [dot_point, objective_of_nonpos h]
    have := neg_le z
    simp only [Pi.sub_apply]
    linarith
  have smid : 0 ≤ x 0 → x 0 ≤ 1 → ∀ z, dot (point 1) (z - x) ≤ objective z - objective x := by
    intro h0 h1 z
    rw [dot_point, objective_of_mid h0 h1]
    have := self_le z
    simp only [Pi.sub_apply]
    linarith
  have sbig : 1 ≤ x 0 → ∀ z, dot (point 2) (z - x) ≤ objective z - objective x := by
    intro h z
    rw [dot_point, objective_of_one_le h]
    have := line_le z
    simp only [Pi.sub_apply]
    linarith
  rcases lt_trichotomy (x 0) 0 with h | h | h
  · exact Or.inl ⟨h, (supporting_vector_eq_gradient (sneg h.le) hg).symm⟩
  · exfalso
    have h1 := supporting_vector_eq_gradient (sneg h.le) hg
    have h2 := supporting_vector_eq_gradient (smid h.ge (by linarith)) hg
    have h3 := congrFun (h1.trans h2.symm) 0
    simp only [point] at h3
    norm_num at h3
  · rcases lt_trichotomy (x 0) 1 with h' | h' | h'
    · exact Or.inr (Or.inl ⟨h, h', (supporting_vector_eq_gradient (smid h.le h'.le) hg).symm⟩)
    · exfalso
      have h1 := supporting_vector_eq_gradient (smid h.le h'.le) hg
      have h2 := supporting_vector_eq_gradient (sbig h'.ge) hg
      have h3 := congrFun (h1.trans h2.symm) 0
      simp only [point] at h3
      norm_num at h3
    · exact Or.inr (Or.inr ⟨h', (supporting_vector_eq_gradient (sbig h'.le) hg).symm⟩)

theorem hasGradient_of_one_lt {x : Vec 1} (h : 1 < x 0) :
    HasFDerivAt objective (gradientFunctional (point 2)) x := by
  have hlin : HasFDerivAt (fun y : Vec 1 => gradientFunctional (point 2) y - 1)
      (gradientFunctional (point 2)) x :=
    (gradientFunctional (point 2)).hasFDerivAt.sub_const 1
  apply hlin.congr_of_eventuallyEq
  have hopen : IsOpen {y : Vec 1 | 1 < y 0} := isOpen_lt continuous_const (continuous_apply 0)
  filter_upwards [hopen.mem_nhds h] with y hy
  have hy' : 1 < y 0 := hy
  rw [objective_of_one_le hy'.le, gradientFunctional_apply, dot_point]

theorem hasGradient_of_mid {x : Vec 1} (h0 : 0 < x 0) (h1 : x 0 < 1) :
    HasFDerivAt objective (gradientFunctional (point 1)) x := by
  have hlin : HasFDerivAt (fun y : Vec 1 => gradientFunctional (point 1) y)
      (gradientFunctional (point 1)) x :=
    (gradientFunctional (point 1)).hasFDerivAt
  apply hlin.congr_of_eventuallyEq
  have hopen : IsOpen {y : Vec 1 | 0 < y 0 ∧ y 0 < 1} :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt (continuous_apply 0) continuous_const)
  filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with y hy
  obtain ⟨hy0, hy1⟩ := hy
  rw [objective_of_mid hy0.le hy1.le, gradientFunctional_apply, dot_point, one_mul]

theorem hasGradient_of_neg {x : Vec 1} (h : x 0 < 0) :
    HasFDerivAt objective (gradientFunctional (point (-1))) x := by
  have hlin : HasFDerivAt (fun y : Vec 1 => gradientFunctional (point (-1)) y)
      (gradientFunctional (point (-1))) x :=
    (gradientFunctional (point (-1))).hasFDerivAt
  apply hlin.congr_of_eventuallyEq
  have hopen : IsOpen {y : Vec 1 | y 0 < 0} := isOpen_lt (continuous_apply 0) continuous_const
  filter_upwards [hopen.mem_nhds h] with y hy
  have hy' : y 0 < 0 := hy
  rw [objective_of_nonpos hy'.le, gradientFunctional_apply, dot_point]
  ring

/-- (RS) fails on $K=\{F\le2\}$: at the level $\eta=1/2$ the pairs $x=1+\varepsilon$,
$z=1-\varepsilon$ have $N^2/T=(1-\varepsilon)^2/(2\varepsilon)\to\infty$. (These pairs have
$t=d/2$, so they are eligible only when $c_2\ge1/2$.) -/
theorem not_rs : ¬ RadialCertificate.HasRadialSecantBounds objective {x | objective x ≤ 2} 0 := by
  intro hRS
  obtain ⟨C, hC⟩ := hRS (1 / 2) (by norm_num)
  set ε : ℝ := 1 / (8 * (|C| + 1)) with hε
  have hA : 0 ≤ |C| := abs_nonneg C
  have hεpos : 0 < ε := by positivity
  have hεle : ε ≤ 1 / 8 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hx0 : (point (1 + ε)) 0 = 1 + ε := rfl
  have hz0 : (point (1 - ε)) 0 = 1 - ε := rfl
  have hgx := hasGradient_of_one_lt (x := point (1 + ε)) (by rw [hx0]; linarith)
  have hgz := hasGradient_of_mid (x := point (1 - ε)) (by rw [hz0]; linarith)
    (by rw [hz0]; linarith)
  have hFx : objective (point (1 + ε)) = 1 + 2 * ε := by
    rw [objective_of_one_le (by rw [hx0]; linarith), hx0]
    ring
  have hFz : objective (point (1 - ε)) = 1 - ε := by
    rw [objective_of_mid (by rw [hz0]; linarith) (by rw [hz0]; linarith), hz0]
  have hcurv : RadialCertificate.secantCurvature (point (1 + ε)) (point (1 - ε)) (point 2)
      (point 1) = 2 * ε := by
    simp only [RadialCertificate.secantCurvature, dot, point, Fin.sum_univ_one, Pi.sub_apply]
    ring
  have hnum : RadialCertificate.radialNumerator 0 (point (1 - ε)) (point 2) (point 1) =
      -(1 - ε) := by
    simp only [RadialCertificate.radialNumerator, dot, point, Fin.sum_univ_one, Pi.sub_apply,
      Pi.zero_apply, sub_zero]
    ring
  have h := hC (point (1 + ε)) (point (1 - ε)) (point 2) (point 1)
    (by show objective _ ≤ 2; rw [hFx]; linarith) (by show objective _ ≤ 2; rw [hFz]; linarith)
    (by rw [objective_zero, hFz]; linarith) (by rw [hFx, hFz]; linarith) hgx hgz
    (by rw [hcurv]; linarith)
  rw [hcurv, hnum] at h
  have hC2 : C * (2 * ε) ≤ |C| * (2 * ε) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have hCε : |C| * (2 * ε) < 1 / 4 := by
    have : |C| * (2 * ε) = |C| / (4 * (|C| + 1)) := by
      rw [hε]
      field_simp
      ring
    rw [this, div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- Every point of $K=\{F\le2\}$ has $-2\le x\le3/2$. -/
theorem sublevel_bounds {x : Vec 1} (hx : objective x ≤ 2) : -2 ≤ x 0 ∧ x 0 ≤ 3 / 2 := by
  have h1 := neg_le x
  have h3 := line_le x
  constructor <;> linarith

/-- (S) for the radial field with $C=6$: for $c_2<1/2$ (any $c_1$), every eligible pair
$x,z\in K=\{F\le2\}$ has $N^2\le6T$, whatever $d$ (a nine-case check on the gradients). -/
theorem radial_secant (c₁ c₂ : ℝ) (hc₂ : c₂ < 1 / 2) {x z g h : Vec 1}
    (hx : objective x ≤ 2) (hz : objective z ≤ 2)
    (hp : TransportedCertificate.EligiblePair objective c₁ c₂ x z g h) :
    (dot (h - g) (z - 0)) ^ 2 ≤ 6 * dot (h - g) (z - x) := by
  have hxK := sublevel_bounds hx
  have hzK := sublevel_bounds hz
  have hd := hp.decrease_pos
  have hcv := hp.curvature
  simp only [TransportedCertificate.pairDecrease, TransportedCertificate.pairCurvature,
    TransportedCertificate.pairStep] at hd hcv
  rcases gradient_cases hp.gradient_x with ⟨hx0, rfl⟩ | ⟨hx0, hx1, rfl⟩ | ⟨hx1, rfl⟩ <;>
  rcases gradient_cases hp.gradient_z with ⟨hz0, rfl⟩ | ⟨hz0, hz1, rfl⟩ | ⟨hz1, rfl⟩ <;>
  simp only [dot, point, Fin.sum_univ_one, Pi.sub_apply, Pi.zero_apply, sub_zero] at hd hcv ⊢ <;>
  nlinarith [hzK.1, hzK.2]

/-- For $c_2<1/2$ (any $c_1$) and every $\eta>0$, the radial field $W(x)=(x-0)(x-0)^T$ with
$m=\eta^2$, $C=6$, $L=0$, $\delta=1$ is a band certificate on $K_\eta$, $K=\{F\le2\}$. -/
theorem radial_certificate (c₁ c₂ : ℝ) (hc₂ : c₂ < 1 / 2) (η : ℝ) (hη : 0 < η) :
    ∃ Cert : TransportedCertificate.BandCertificate objective {x | objective x ≤ 2}
        (objective 0) c₁ c₂ η,
      Cert.W = (fun x => outer (x - 0) (x - 0)) ∧ Cert.m = η ^ 2 ∧ Cert.C = 6 ∧ Cert.L = 0 := by
  refine ⟨TransportedCertificate.rankOneCertificate (fun x => x - 0) (η ^ 2) 6 0 1
    (by positivity) le_rfl zero_lt_one ?_ ?_ ?_, rfl, rfl, rfl, rfl⟩
  · intro x hx g hg
    have hs := convex_supporting_inequality objective_convex hg 0
    have he : dot g (0 - x) = -dot g (x - 0) := by
      unfold dot
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [he] at hs
    have hgap : η ≤ dot g (x - 0) := by linarith [hx.2]
    nlinarith
  · intro x z g h hx hz hp _
    exact radial_secant c₁ c₂ hc₂ hx.1 hz.1 hp
  · intro x z g h _ _ _ _
    refine ⟨1, 1, ?_, ?_⟩
    · simp only [one_smul, TransportedCertificate.pairStep]
      abel
    · simp

end Kink

/-- Item `C/03_T/prose/029` (`companion/chapters/03_T.tex:225-225`), the counterexample to the
literal reading of "Condition (S) is exactly (RS)": (S) for the radial field does not give (RS).
For $F(x)=\max\{|x|,2x-1\}$ on $\R$ (finite, convex, unique minimizer $x_*=0$, $F_*=0$, compact
$K=\{F\le2\}$) and every pair with $c_2<1/2$: (S) holds for $W(x)=(x-x_*)(x-x_*)^T$ with $C_\eta=6$
on every band $K_\eta$ (for every eligible pair, whatever $d$), and the radial field is a band
certificate ($m=\eta^2$, $C=6$, $L=0$, $\delta=1$) on every band, so $K$ admits the band
certificates of the theorem; yet (RS) fails on $K$ (at $\eta=1/2$, the pairs $x=1+\varepsilon$,
$z=1-\varepsilon$ have $N^2/T=(1-\varepsilon)^2/(2\varepsilon)\to\infty$; they are not eligible,
as $t=d/2<(1-c_2)d$). -/
theorem s_not_exactly_rs :
    ∃ F : Vec 1 → ℝ, (∀ x, F x = max |x 0| (2 * x 0 - 1)) ∧ ConvexOn ℝ Set.univ F ∧
      (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧ IsCompact {x | F x ≤ 2} ∧
      (∀ c₁ c₂ : ℝ, c₂ < 1 / 2 → ∀ η : ℝ, 0 < η →
        ∀ x ∈ {x | x ∈ {x | F x ≤ 2} ∧ F x ≥ F 0 + η},
        ∀ z ∈ {x | x ∈ {x | F x ≤ 2} ∧ F x ≥ F 0 + η}, ∀ g h : Vec 1,
          TransportedCertificate.EligiblePair F c₁ c₂ x z g h →
          dot (h - g) (outer (z - 0) (z - 0) *ᵥ (h - g)) ≤ 6 * dot (h - g) (z - x)) ∧
      (∀ c₁ c₂ : ℝ, c₂ < 1 / 2 → ∀ η : ℝ, 0 < η →
        ∃ Cert : TransportedCertificate.BandCertificate F {x | F x ≤ 2} (F 0) c₁ c₂ η,
          Cert.W = (fun x => outer (x - 0) (x - 0)) ∧ Cert.m = η ^ 2 ∧ Cert.C = 6 ∧
            Cert.L = 0) ∧
      (∀ c₁ c₂ : ℝ, c₂ < 1 / 2 →
        TransportedCertificate.HasBandCertificates F {x | F x ≤ 2} (F 0) c₁ c₂) ∧
      ¬ RadialCertificate.HasRadialSecantBounds F {x | F x ≤ 2} 0 :=
  ⟨Kink.objective, Kink.objective_eq_abs, Kink.objective_convex, Kink.objective_min,
    Kink.objective_unique,
    Localization.sublevel_compact Kink.objective_convex 0 Kink.objective_min
      Kink.objective_unique 2,
    fun c₁ c₂ hc₂ _ _ x hx z hz g h hp => by
      rw [radial_field_energy]
      exact Kink.radial_secant c₁ c₂ hc₂ hx.1 hz.1 hp,
    Kink.radial_certificate,
    fun c₁ c₂ hc₂ η hη _ => (Kink.radial_certificate c₁ c₂ hc₂ η hη).elim fun Cert _ => ⟨Cert⟩,
    Kink.not_rs⟩

/-- Item `C/03_T/disp/028` (`companion/chapters/03_T.tex:226-228`): with $s=z-x$,
$\Pi_s(z-x_*)=\Pi_s(x-x_*)$. -/
theorem radial_projection {n : ℕ} (xstar x z : Vec n) :
    TransportedCertificate.stepProjector (z - x) *ᵥ (z - xstar) =
      TransportedCertificate.stepProjector (z - x) *ᵥ (x - xstar) := by
  have h : z - xstar = (x - xstar) + (z - x) := by abel
  rw [h, Matrix.mulVec_add, TransportedCertificate.stepProjector_mulVec_self, add_zero]

/-- Item `C/03_T/prose/030` (`companion/chapters/03_T.tex:225-229`): "[display 028] makes (T) an
equality with $L=0$." For $W(x)=(x-x_*)(x-x_*)^T$ and $s=z-x$:
$\Pi_sW(z)\Pi_s=\Pi_sW(x)\Pi_s$, so (T) holds with $L=0$ (for every $d$). -/
theorem radial_transport_equality {n : ℕ} (xstar x z : Vec n) (d : ℝ) :
    TransportedCertificate.stepProjector (z - x) * outer (z - xstar) (z - xstar) *
        TransportedCertificate.stepProjector (z - x) =
      TransportedCertificate.stepProjector (z - x) * outer (x - xstar) (x - xstar) *
        TransportedCertificate.stepProjector (z - x) ∧
      ((1 + 0 * d) • (TransportedCertificate.stepProjector (z - x) * outer (x - xstar) (x - xstar) *
          TransportedCertificate.stepProjector (z - x)) -
        TransportedCertificate.stepProjector (z - x) * outer (z - xstar) (z - xstar) *
          TransportedCertificate.stepProjector (z - x)).PosSemidef := by
  have heq : TransportedCertificate.stepProjector (z - x) * outer (z - xstar) (z - xstar) *
        TransportedCertificate.stepProjector (z - x) =
      TransportedCertificate.stepProjector (z - x) * outer (x - xstar) (x - xstar) *
        TransportedCertificate.stepProjector (z - x) := by
    rw [TransportedCertificate.projected_outer, TransportedCertificate.projected_outer,
      radial_projection]
  refine ⟨heq, ?_⟩
  rw [heq, zero_mul, add_zero, one_smul, sub_self]
  exact Matrix.PosSemidef.zero

/-- Item `C/03_T/prose/031` (`companion/chapters/03_T.tex:229-229`): "Thus every objective
covered by RS is covered by the new condition." For finite convex $F$ with minimizer $x_*$ and
(RS) on $K$: for every pair $0<c_1$, $c_2<1$ and every $\eta>0$ there is a band certificate on
$K_\eta$ with field $W(x)=(x-x_*)(x-x_*)^T$, $m=\eta^2$ and $L=0$; so $K$ admits the band
certificates of the theorem. -/
theorem rs_covered {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ Set.univ F) (xstar : Vec n)
    (_hmin : ∀ x, F xstar ≤ F x) (K : Set (Vec n))
    (hRS : RadialCertificate.HasRadialSecantBounds F K xstar)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) :
    (∀ η : ℝ, 0 < η → ∃ Cert : TransportedCertificate.BandCertificate F K (F xstar) c₁ c₂ η,
        Cert.W = (fun x => outer (x - xstar) (x - xstar)) ∧ Cert.m = η ^ 2 ∧ Cert.L = 0) ∧
      TransportedCertificate.HasBandCertificates F K (F xstar) c₁ c₂ := by
  have hcert : ∀ η : ℝ, 0 < η → ∃ Cert : TransportedCertificate.BandCertificate F K (F xstar)
      c₁ c₂ η, Cert.W = (fun x => outer (x - xstar) (x - xstar)) ∧ Cert.m = η ^ 2 ∧
        Cert.L = 0 := by
    intro η hη
    obtain ⟨C, hC⟩ := hRS η hη
    refine ⟨TransportedCertificate.rankOneCertificate (fun x => x - xstar) (η ^ 2) C 0 1
      (sq_pos_of_pos hη) le_rfl zero_lt_one ?_ ?_ ?_, rfl, rfl, rfl⟩
    · intro x hx g hg
      have hs := convex_supporting_inequality hF hg xstar
      have he : dot g (xstar - x) = -dot g (x - xstar) := by
        unfold dot
        simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring
      rw [he] at hs
      have hgap : η ≤ dot g (x - xstar) := by linarith [hx.2]
      nlinarith
    · intro x z g h hx hz e _
      have hdec : F z ≤ F x := by
        have hp := mul_pos hc₁ e.decrease_pos
        linarith [e.armijo]
      exact hC x z g h hx.1 hz.1 hz.2 hdec e.gradient_x e.gradient_z
        (TransportedCertificate.eligible_curvature_pos e hc₂)
    · intro x z g h _ _ _ _
      refine ⟨1, 1, ?_, ?_⟩
      · simp only [one_smul, TransportedCertificate.pairStep]
        abel
      · simp
  exact ⟨hcert, fun η hη _ => (hcert η hη).elim fun Cert _ => ⟨Cert⟩⟩

/-- Item `C/03_T/prose/032` (`companion/chapters/03_T.tex:231-231`): "The reverse implication
fails. Chapter~\ref{comp:Q} constructs fields satisfying the new condition for a multi-branch
curved objective that violates even the eligible-pair radial condition on every positive
neighborhood of its minimizer." The three-branch parabolic objective of Chapter~Q,
$F(u,v)=\max\{u^2+v,3u^2,2u^2-v\}$ (`Parabolic.Example.objective`, equation (10.18)), is finite and
convex with unique minimizer $0$, $F(0)=0$, and compact sublevels; every compact $K$ admits the
band certificates of the theorem for every pair $0<c_1$, $c_2<1$ (the field (10.8),
`Parabolic.Family.exists_bandCertificate`); yet on every neighborhood $K$ of $0$ (RS) fails, and,
for every fixed $0<c_1<c_2<1$, there is a positive band on which even the eligible pairs with
arbitrarily small $d$ violate every proposed radial bound $N^2\le Ct$. -/
theorem rs_strictly_weaker :
    ∃ F : Vec 2 → ℝ,
      (∀ x, F x = max (max ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)) (2 * (x 0) ^ 2 - x 1)) ∧
      ConvexOn ℝ Set.univ F ∧ F 0 = 0 ∧ (∀ x, F 0 ≤ F x) ∧ (∀ x, F x = F 0 → x = 0) ∧
      (∀ b : ℝ, IsCompact {x | F x ≤ b}) ∧
      (∀ K : Set (Vec 2), IsCompact K → ∀ c₁ c₂ : ℝ, 0 < c₁ → c₂ < 1 →
        TransportedCertificate.HasBandCertificates F K 0 c₁ c₂) ∧
      (∀ K : Set (Vec 2), K ∈ 𝓝 (0 : Vec 2) → ¬ RadialCertificate.HasRadialSecantBounds F K 0) ∧
      (∀ K : Set (Vec 2), K ∈ 𝓝 (0 : Vec 2) → ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → c₂ < 1 →
        ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → ∀ C : ℝ, ∃ x z g h : Vec 2,
          x ∈ K ∧ z ∈ K ∧ F 0 + η ≤ F z ∧ F z ≤ F x ∧
          TransportedCertificate.EligiblePair F c₁ c₂ x z g h ∧ -dot g (z - x) ≤ δ ∧
          C * dot (h - g) (z - x) < (dot (h - g) (z - 0)) ^ 2) := by
  refine ⟨Parabolic.Example.objective, Parabolic.Example.objective_eq_max,
    Parabolic.Example.family.objective_convex, Parabolic.Example.family.objective_zero,
    Parabolic.Example.family.unique_minimum.1, Parabolic.Example.family.unique_minimum.2,
    Parabolic.Example.family.sublevel_compact, fun K hK c₁ c₂ hc₁ hc₂ =>
      Parabolic.Example.family.hasBandCertificates hK hc₁.le hc₂,
    fun K hK => Parabolic.Example.not_radial_secant_on_neighborhood hK, ?_⟩
  intro K hK c₁ c₂ hc₁ hc₁₂ hc₂
  obtain ⟨η, hη, h⟩ := Parabolic.Example.eligible_radial_unbounded_on_neighborhood hK
    (by linarith : c₁ < 1) (by linarith : 0 ≤ c₂)
  refine ⟨η, hη, fun δ hδ C => ?_⟩
  obtain ⟨x, z, g, h', _H, hx, hz, hFz, hFzx, hp, hd, -, -, hC⟩ := h δ hδ C
  have h0 : Parabolic.Example.objective 0 = 0 := Parabolic.Example.family.objective_zero
  exact ⟨x, z, g, h', hx, hz, by rw [h0, zero_add]; exact hFz, hFzx, hp, hd, hC⟩

/-- Item `C/03_T/disp/029` (`companion/chapters/03_T.tex:234-236`): "Although $\Pi_s$ is written
as a Euclidean projector, (T) equivalently requires
$a^TW(z)a\le(1+Ld)a^TW(x)a$ for every $a$ with $a^Ts=0$." For symmetric $W(x),W(z)$ (in
the theorem $W$ is PSD, hence symmetric, at the differentiable endpoints of eligible pairs). -/
theorem transport_perpendicular {n : ℕ} (Wx Wz : Mat n) (hWx : Wx.IsSymm) (hWz : Wz.IsSymm)
    (s : Vec n) (L d : ℝ) :
    ((1 + L * d) • (TransportedCertificate.stepProjector s * Wx *
        TransportedCertificate.stepProjector s) -
      TransportedCertificate.stepProjector s * Wz *
        TransportedCertificate.stepProjector s).PosSemidef
      ↔ ∀ a : Vec n, dot a s = 0 → dot a (Wz *ᵥ a) ≤ (1 + L * d) * dot a (Wx *ᵥ a) :=
  TransportedCertificate.projected_transport_iff_perpendicular Wx Wz hWx hWz s (1 + L * d)

/-- Item `C/03_T/prose/034` (`companion/chapters/03_T.tex:237-237`): "Under an invertible affine
change of variables with linear part $A$, gradients transform by $A^{-\mathsf T}$ and the
certificate transforms by $W\mapsto AWA^T$. The three conditions are therefore affine-covariant;
no preferred coordinate system is essential." For $\det A\ne0$, the new variable $z=Ax+b$
(`forward A b`) and the transformed objective $\tilde F(z)=F(A^{-1}(z-b))$: a gradient $g$ of $F$
at $x$ becomes the gradient $A^{-T}g$ of $\tilde F$ at $Ax+b$; eligibility is preserved exactly;
every band certificate of $F$ on $K$ gives one of $\tilde F$ on the image of $K$ with field
$\tilde W(Ax+b)=AW(x)A^T$ and the same constants $m,C,L,\delta$; and $K$ admits the band
certificates iff its image does. -/
theorem affine_covariance {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (b : Vec n) (F : Vec n → ℝ)
    (K : Set (Vec n)) (Fstar c₁ c₂ : ℝ) :
    (∀ z, AffineCertificate.objective A b F z = F (A⁻¹ *ᵥ (z - b))) ∧
      (∀ x, AffineCertificate.forward A b x = A *ᵥ x + b) ∧
      (∀ x g : Vec n, HasFDerivAt F (gradientFunctional g) x →
        HasFDerivAt (AffineCertificate.objective A b F) (gradientFunctional ((A⁻¹)ᵀ *ᵥ g))
          (AffineCertificate.forward A b x)) ∧
      (∀ x z g h : Vec n, TransportedCertificate.EligiblePair F c₁ c₂ x z g h ↔
        TransportedCertificate.EligiblePair (AffineCertificate.objective A b F) c₁ c₂
          (AffineCertificate.forward A b x) (AffineCertificate.forward A b z)
          ((A⁻¹)ᵀ *ᵥ g) ((A⁻¹)ᵀ *ᵥ h)) ∧
      (∀ (η : ℝ) (Cert : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η),
        ∃ Cert' : TransportedCertificate.BandCertificate (AffineCertificate.objective A b F)
            (AffineCertificate.forward A b '' K) Fstar c₁ c₂ η,
          (∀ x, Cert'.W (AffineCertificate.forward A b x) = A * Cert.W x * Aᵀ) ∧
            Cert'.m = Cert.m ∧ Cert'.C = Cert.C ∧ Cert'.L = Cert.L ∧ Cert'.δ = Cert.δ) ∧
      (TransportedCertificate.HasBandCertificates F K Fstar c₁ c₂ ↔
        TransportedCertificate.HasBandCertificates (AffineCertificate.objective A b F)
          (AffineCertificate.forward A b '' K) Fstar c₁ c₂) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun x g hg => ?_,
    fun x z g h => AffineCertificate.eligible_pair_affine_iff A hA b x z g h,
    fun η Cert => ⟨AffineCertificate.transform A hA b Cert,
      AffineCertificate.transform_field A hA b Cert, rfl, rfl, rfl, rfl⟩,
    AffineCertificate.hasBandCertificates_affine_iff A hA b F K Fstar c₁ c₂⟩
  have hg' : HasFDerivAt F (gradientFunctional g)
      (AffineCertificate.backward A b (AffineCertificate.forward A b x)) := by
    rwa [AffineCertificate.backward_forward A hA]
  exact AffineCertificate.transformed_gradient A b hg'

/-- Item `C/03_T/prose/035` (`companion/chapters/03_T.tex:239-239`): "The extra transport clause
cannot simply be omitted: changing a comparison vector creates terms involving $B_k$, which may be
unbounded. A small Euclidean change is not by itself a small change in the $B_k$ energy." There
are SPD matrices $B_k=\operatorname{diag}(1,(k+1)^4)$ (unbounded) and vectors $v_k\to v$ with
$v^TB_kv=1$ for all $k$ but $v_k^TB_kv_k-v^TB_kv\to\infty$ (library
`ComparisonEnergyWarning.comparisonEnergyWarning`; an algebraic example, not a BFGS run). -/
theorem energy_warning :
    ∃ (B : ℕ → Mat 2) (v : ℕ → Vec 2) (v₀ : Vec 2), (∀ k, (B k).PosDef) ∧
      Tendsto v atTop (𝓝 v₀) ∧ (∀ k, dot v₀ (B k *ᵥ v₀) = 1) ∧
      Tendsto (fun k => B k 1 1) atTop atTop ∧
      Tendsto (fun k => dot (v k) (B k *ᵥ v k) - dot v₀ (B k *ᵥ v₀)) atTop atTop := by
  refine ⟨ComparisonEnergyWarning.hessian, ComparisonEnergyWarning.moving,
    ComparisonEnergyWarning.reference, ComparisonEnergyWarning.hessian_posDef,
    ComparisonEnergyWarning.moving_tendsto_reference, ComparisonEnergyWarning.reference_energy,
    ?_, ComparisonEnergyWarning.energy_increase_tendsto⟩
  have he : (fun k => ComparisonEnergyWarning.hessian k 1 1) = fun k : ℕ => ((k : ℝ) + 1) ^ 4 := by
    funext k
    simp [ComparisonEnergyWarning.hessian]
  rw [he]
  exact (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-! ### Non-vacuity

The examples use the article's quadratic example `BfgsCoverage.Article.Energy.Example`:
$F(x)=x^2/2$ on $\R$, its admissible run $x_k=2^{-k}$ (`run`, constants $(1/4,3/4)$) and its band
certificates `quadCert` ($W=I$, $m=2\eta$, $C=1$, $L=0$, $\delta=1$). -/

namespace Example
open BfgsCoverage.Article.Energy.Example

theorem quad_zero : quad 0 = 0 := by simp [quad]

theorem quad_min : ∀ x, quad 0 ≤ quad x := fun x => by
  rw [quad_zero]
  exact quad_nonneg x

theorem quad_unique : ∀ x, quad x = quad 0 → x = 0 := by
  intro x hx
  rw [quad_zero] at hx
  funext i
  fin_cases i
  simp only [quad] at hx
  simpa using hx

/-- `quad` admits the band certificates on every set, for all constants. -/
theorem quad_certs (K : Set (Vec 1)) (c₁ c₂ : ℝ) :
    TransportedCertificate.HasBandCertificates quad K 0 c₁ c₂ :=
  fun η hη _ => ⟨quadCert K c₁ c₂ η hη⟩

/-- `quad` satisfies (RS) on every sublevel $\{F\le b\}$, with $C_\eta=2b$:
$N^2=(z-x)^2z^2\le2b(z-x)^2=2bT$. -/
theorem quad_rs (b : ℝ) : RadialCertificate.HasRadialSecantBounds quad {x | quad x ≤ b} 0 := by
  intro η _
  refine ⟨2 * b, fun x z g h _ hz _ _ hg hh _ => ?_⟩
  have hg' := quad_grad_eq hg
  have hh' := quad_grad_eq hh
  rw [hg', hh']
  have hz' : z 0 ^ 2 / 2 ≤ b := hz
  simp only [RadialCertificate.radialNumerator, RadialCertificate.secantCurvature, dot,
    Fin.sum_univ_one, Pi.sub_apply, Pi.zero_apply, sub_zero]
  have hprod := mul_nonneg (sq_nonneg (z 0 - x 0)) (by linarith : (0 : ℝ) ≤ 2 * b - z 0 ^ 2)
  nlinarith

/-- A potential certificate with $\Psi=0$ from any band certificate ($e^{Ld}\ge1+Ld$). -/
def potentialOf {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {Fstar c₁ c₂ η : ℝ}
    (C : TransportedCertificate.BandCertificate F K Fstar c₁ c₂ η) :
    TransportedCertificate.PotentialBandCertificate F K Fstar c₁ c₂ η where
  W := C.W
  Ψ := fun _ => 0
  m := C.m
  C := C.C
  L := C.L
  δ := C.δ
  ψlo := 0
  ψhi := 0
  m_pos := C.m_pos
  L_nonneg := C.L_nonneg
  delta_pos := C.delta_pos
  potential_bounds := fun _ _ => ⟨le_rfl, le_rfl⟩
  positive_semidefinite := C.positive_semidefinite
  visibility := C.visibility
  secant := C.secant
  transport := fun x z g h hx hz hp hd => by
    have hX := TransportedCertificate.projected_psd
      (C.positive_semidefinite x hx hp.gradient_x.differentiableAt)
      (TransportedCertificate.pairStep x z)
    have h := TransportedCertificate.scale_loewner hX zero_le_one (C.transport x z g h hx hz hp hd)
      (v := Real.exp (C.L * TransportedCertificate.pairDecrease x z g + 0 - 0)) (by
        rw [add_zero, sub_zero, one_mul, add_comm]
        exact Real.add_one_le_exp _)
    simpa only [one_smul] using h

end Example

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of Theorem `C/03_T/theorem/001` (`one_sided_convergence`; its certificate
hypothesis is `HasBandCertificates`, by `hasBandCertificates_iff`) can all hold at once:
$F(x)=x^2/2$, $F_*=0$, $b=1$, $K=\{F\le1\}$, the run $x_k=2^{-k}$. The same data satisfy the
hypotheses of the proof displays up to `C/03_T/disp/017`. -/
example : ∃ (F : Vec 1 → ℝ) (Fstar b : ℝ) (K : Set (Vec 1)) (R : AdmissibleBFGSRun 1 F),
    IsLeast (Set.range F) Fstar ∧ K = {x | F x ≤ b} ∧ b > Fstar ∧ IsCompact K ∧
      TransportedCertificate.HasBandCertificates F K Fstar R.c₁ R.c₂ ∧ R.x 0 ∈ K := by
  refine ⟨quad, 0, 1, _, run, quad_isLeast, rfl, one_pos, quad_sublevel_compact 1,
    Example.quad_certs _ _ _, ?_⟩
  show quad (pt 0) ≤ 1
  simp [quad, pt]
  norm_num

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of the general forms of the proof displays (`trace_step_general`,
`C_nonneg_of_pair`, `enlarged_recurrence`, `quadratic_budget_finite`, and the article's
`certificate_budget_general` used for display `C/03_T/disp/021`) can all hold at once: the
quadratic run, $K=\R$, $F_*=0$, $\eta=1/8$, $k=0$, $N=1$. -/
example : ∃ (F : Vec 1 → ℝ) (R : AdmissibleBFGSRun 1 F) (K : Set (Vec 1)) (Fstar η : ℝ)
    (Cert : TransportedCertificate.BandCertificate F K Fstar R.c₁ R.c₂ η) (E a : ℕ → ℝ)
    (M : ℕ → Mat 1) (k N : ℕ),
    (∀ k, E k = (R.hessian k * Cert.W (R.x k)).trace) ∧ (∀ k, a k = 1 + Cert.L * R.d k) ∧
      (∀ k, M k = R.hessian k - (R.q k)⁻¹ • outer (R.g k) (R.g k)) ∧
      R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η} ∧ R.x (k + 1) ∈ {x | x ∈ K ∧ F x ≥ Fstar + η} ∧
      R.d k ≤ Cert.δ ∧ Summable R.d ∧ (∀ k, k ≤ N → R.x k ∈ {x | x ∈ K ∧ F x ≥ Fstar + η}) ∧
      ∀ k, k < N → R.d k ≤ Cert.δ := by
  have hd0 : run.d 0 ≤ 1 := by rw [run_d]; norm_num
  refine ⟨quad, run, Set.univ, 0, 1 / 8, quadCert _ _ _ (1 / 8) (by norm_num), _, _, _, 0, 1,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, pt_band 0 (by norm_num), pt_band 1 le_rfl, hd0,
    run_summable, fun k hk => pt_band k hk, fun k hk => ?_⟩
  obtain rfl : k = 0 := by omega
  exact hd0

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of the local statements (`outside_neighborhood_gap`, `local_basin`,
`solution_set_basin`, `structural_region_convergence`, `shell_convergence`) can hold at once:
$F(x)=x^2/2$ with unique minimizer $0$, $b=1$, $K=\{F\le1\}$, $U=\R$, certificates on $K\cap U$
(hence shell certificates, `shell_certificates`), and an admissible run with the constants
$(1/4,3/4)$ starting in $K$, whose initial sublevel is compact and lies in $U$. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (b : ℝ) (K U : Set (Vec 1)) (c₁ c₂ : ℝ)
    (R : AdmissibleBFGSRun 1 F),
    ConvexOn ℝ Set.univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      F xstar < b ∧ K = {x | F x ≤ b} ∧ IsCompact K ∧ U ∈ 𝓝 xstar ∧
      (∀ x, F x = F xstar → U ∈ 𝓝 x) ∧
      TransportedCertificate.HasBandCertificates F (K ∩ U) (F xstar) c₁ c₂ ∧
      TransportedCertificate.HasShellCertificates F K (F xstar) c₁ c₂ ∧
      R.c₁ = c₁ ∧ R.c₂ = c₂ ∧ R.x 0 ∈ K ∧ IsCompact {x | F x ≤ F (R.x 0)} ∧
      {x | F x ≤ F (R.x 0)} ⊆ U := by
  refine ⟨quad, 0, 1, _, Set.univ, 1 / 4, 3 / 4, run, quad_convex, Example.quad_min,
    Example.quad_unique, by rw [Example.quad_zero]; norm_num, rfl, quad_sublevel_compact 1,
    Filter.univ_mem, fun _ _ => Filter.univ_mem, ?_, ?_, rfl, rfl, ?_, quad_sublevel_compact _,
    Set.subset_univ _⟩
  · rw [Example.quad_zero]
    exact Example.quad_certs _ _ _
  · rw [Example.quad_zero]
    exact shell_certificates 0 _ _ _ (Example.quad_certs _ _ _)
  · show quad (pt 0) ≤ 1
    simp [quad, pt]
    norm_num

open BfgsCoverage.Article.Energy.Example in
/-- The hypotheses of the statements about (RS) (`radial_visibility`, `radial_secant_exact`,
`rs_gives_s`, `rs_covered`) can hold at once: $F(x)=x^2/2$ with minimizer $0$ satisfies (RS) on
$K=\{F\le1\}$ (`quad_rs`; the hypothesis of `rs_gives_s` is (RS) at one level, `rs_iff`),
$\eta=1/8$, $x=1$ (in $K_{1/8}$, gradient $1$), and the eligible accepted pair $(x_0,x_1)=(1,1/2)$
of the quadratic run, which lies in $K_{1/8}$. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (b η : ℝ) (K : Set (Vec 1)) (x g : Vec 1)
    (R : AdmissibleBFGSRun 1 F),
    ConvexOn ℝ Set.univ F ∧ (∀ x, F xstar ≤ F x) ∧ K = {x | F x ≤ b} ∧ IsCompact K ∧
      RadialCertificate.HasRadialSecantBounds F K xstar ∧ 0 < η ∧
      x ∈ {x | x ∈ K ∧ F x ≥ F xstar + η} ∧ HasFDerivAt F (gradientFunctional g) x ∧
      R.x 0 ∈ {x | x ∈ K ∧ F x ≥ F xstar + η} ∧ R.x 1 ∈ {x | x ∈ K ∧ F x ≥ F xstar + η} ∧
      TransportedCertificate.EligiblePair F R.c₁ R.c₂ (R.x 0) (R.x 1) (R.g 0) (R.g 1) := by
  have hb : ∀ k, k ≤ 1 → run.x k ∈ {x | x ∈ {x | quad x ≤ 1} ∧ quad x ≥ quad 0 + 1 / 8} := by
    intro k hk
    rw [Example.quad_zero]
    refine ⟨?_, (pt_band k hk).2⟩
    show quad (pt k) ≤ 1
    interval_cases k <;> norm_num [quad, pt]
  refine ⟨quad, 0, 1, 1 / 8, _, run.x 0, run.g 0, run, quad_convex, Example.quad_min, rfl,
    quad_sublevel_compact 1, Example.quad_rs 1, by norm_num, hb 0 (by norm_num),
    run.hasGradient 0, hb 0 (by norm_num), hb 1 le_rfl, run.accepted_pair_eligible 0⟩

/-- A potential certificate (the hypothesis of `potential_absorption`) exists: $\Psi=0$ with
the quadratic band certificate. Two certificates on one band exist (the hypothesis of
`certificate_sum`). -/
example : ∃ (K : Set (Vec 1)) (η : ℝ),
    Nonempty (TransportedCertificate.PotentialBandCertificate
      BfgsCoverage.Article.Energy.Example.quad K 0 (1 / 4) (3 / 4) η) ∧
    Nonempty (TransportedCertificate.BandCertificate
      BfgsCoverage.Article.Energy.Example.quad K 0 (1 / 4) (3 / 4) η) :=
  ⟨Set.univ, 1, ⟨Example.potentialOf (BfgsCoverage.Article.Energy.Example.quadCert _ _ _ 1
    one_pos)⟩, ⟨BfgsCoverage.Article.Energy.Example.quadCert _ _ _ 1 one_pos⟩⟩

/-- The condition (S) in `s_not_exactly_rs` is not vacuous: for $(c_1,c_2)=(1/8,1/4)$ the points
$x=1/2$ and $z=-1/4$ of $K_{1/4}$ ($K=\{F\le2\}$, $F(x)=1/2$, $F(z)=1/4$) form an eligible pair,
with $d=3/4\le\delta=1$, on which (S) reads $N^2=1/4\le6t=9$. -/
example : Kink.point (1 / 2) ∈ {x | x ∈ {x | Kink.objective x ≤ 2} ∧
      Kink.objective x ≥ Kink.objective 0 + 1 / 4} ∧
    Kink.point (-1 / 4) ∈ {x | x ∈ {x | Kink.objective x ≤ 2} ∧
      Kink.objective x ≥ Kink.objective 0 + 1 / 4} ∧
    TransportedCertificate.EligiblePair Kink.objective (1 / 8) (1 / 4) (Kink.point (1 / 2))
      (Kink.point (-1 / 4)) (Kink.point 1) (Kink.point (-1)) ∧
    -dot (Kink.point 1) (Kink.point (-1 / 4) - Kink.point (1 / 2)) ≤ 1 := by
  have hx : Kink.objective (Kink.point (1 / 2)) = 1 / 2 := by
    rw [Kink.objective_of_mid (x := Kink.point (1 / 2)) (by norm_num [Kink.point])
      (by norm_num [Kink.point])]
    norm_num [Kink.point]
  have hz : Kink.objective (Kink.point (-1 / 4)) = 1 / 4 := by
    rw [Kink.objective_of_nonpos (x := Kink.point (-1 / 4)) (by norm_num [Kink.point])]
    norm_num [Kink.point]
  refine ⟨?_, ?_, ⟨Kink.hasGradient_of_mid (by norm_num [Kink.point]) (by norm_num [Kink.point]),
    Kink.hasGradient_of_neg (by norm_num [Kink.point]), ?_, ?_, ?_, ?_⟩, ?_⟩
  · show Kink.objective _ ≤ 2 ∧ Kink.objective _ ≥ Kink.objective 0 + 1 / 4
    rw [hx, Kink.objective_zero]
    norm_num
  · show Kink.objective _ ≤ 2 ∧ Kink.objective _ ≥ Kink.objective 0 + 1 / 4
    rw [hz, Kink.objective_zero]
    norm_num
  all_goals (try rw [hx, hz])
  all_goals simp only [TransportedCertificate.pairDecrease, TransportedCertificate.pairCurvature,
    TransportedCertificate.pairStep, dot, Kink.point, Fin.sum_univ_one, Pi.sub_apply]
  all_goals norm_num

end BfgsCoverage.Companion.Ch03T
