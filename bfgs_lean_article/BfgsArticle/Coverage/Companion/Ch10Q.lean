import BfgsArticle.Coverage.Article.Energy
import BfgsArticle.Coverage.Article.Global
import BfgsVerification.DEmbeddingObjective
import BfgsVerification.ParabolicCertificate
import BfgsVerification.ParabolicEnvelopeBreakpoints
import BfgsVerification.ParabolicEnvelopePrunedFamily
import BfgsVerification.ParabolicEnvelopeBound
import BfgsVerification.ParabolicExampleContrast
import BfgsVerification.ParabolicExampleScale
import BfgsVerification.ParabolicExampleSeparation
import BfgsVerification.ParabolicExampleSourceIdentities
import BfgsVerification.UnexcitedMetric
import BfgsArticle.AdmissibleRunExistence

/-!
# Lean coverage: `companion/chapters/10_Q.tex`

Chapter Q ("Flat contours and parabolic branches") of the companion: the theorem on finite
multi-branch parabolic maxima, the normalized upper envelope and the calibrated scale
(10.7)-(10.8), the visibility and secant identities (10.9)-(10.12), the denominator estimate
(10.13)-(10.14), the transport estimates (10.15)-(10.17), the explicit three-branch example (10.18)
with its printed scale, its accepted unit steps and the failure of (RS), and the claims of the
surrounding text. Register: `editorial/lean_coverage/register/C_10_Q.json`.

## Conventions

* $(u,v)$ is `x : Vec 2` with $u=$ `x 0`, $v=$ `x 1` (for $z$: $u'$, $v'$); $a^Tb$ is `dot a b`,
  $ab^T$ is `outer a b`, $Mv$ is `M *ᵥ v`.
* The finite parabolic maximum with $a_i>0$, $\min_ib_i<0<\max_ib_i$ is `P.objective` for
  `P : Parabolic.Family m` (`objective_isGreatest`); the theorem itself is stated with explicit
  coefficients (`family_objective_eq`). Branch $i$ is active at $x$ (`P.Active i x`) when
  $F(x)=a_iu^2+b_iv$.
* An infinite admissible unmodified full-BFGS run is `R : AdmissibleBFGSRun 2 F` (the
  convention of `01_I.tex:40-47`: arbitrary $H_0\succ0$, fixed $0<c_1<c_2<1$, differentiable
  accepted iterates).
* A pair is $x$, $z$ with gradients $g$, $g'$ and $y=g'-g$; $s=z-x$, $d=-g^Ts$, $t=y^Ts$ are
  `pairStep`, `pairDecrease`, `pairCurvature`, and $\Delta=F(x)-F(z)$ is written out; $h$,
  $\ell$, $D$, $\lambda$, $\widetilde\lambda$, $\Pi_s$ are `horizontalStep`, `normalStep`,
  `stepDeterminant`, `quotientMultiplier`, `compensatedMultiplier`, `stepProjector`. An eligible
  pair (differentiable endpoints, $d>0$, Armijo, $\Delta\le d$, weak Wolfe) is
  `EligiblePair F c₁ c₂ x z g g'`.
* $r$, $\theta$, $\theta r$ are `radialDirection`, `calibratedScale`, `calibratedVector`, and
  $W=\theta^2rr^T$ is `outer (calibratedVector x) (calibratedVector x)`; the constants $k_i$ are
  `calibration i`. The positive band is $\{\eta\le F\le B\}$, $\eta>0$.
* "Uniformly on the band for sufficiently small eligible $d$" and $O(d)$: constants and a
  threshold $\delta>0$ chosen before the pairs (from the family, $\eta$, $B$, $c_1$, $c_2$), and
  the estimate for every eligible pair in the band with $d\le\delta$. Limits as
  $\epsilon\downarrow0$ are along `𝓝[>] 0`.
* Objects introduced by the text ($e$, $\bar e$, $h$, $N$, $A_i$, $\varphi$, $L_i$, $t_0$, $v_0$,
  $S$, the segments $S_k$, $\lambda$, $\widetilde\lambda$, the example's $F$, $\theta$, $k_i$ and
  $W$, $x_\epsilon$, $z_\epsilon$, $H_\epsilon$, $z_{\epsilon,\rho}$, $H_{\epsilon,\rho}$, $\rho$)
  are variables with their defining equations; a hypothesis whose name starts with `_` is a
  standing assumption that the Lean proof does not use.

## Items

* `theorem/001` with `disp/001`, `disp/002` (lines 37-48): `parabolic_convergence`,
  `essential_branches_arbitrary`, `flat_branch_allowed`.
* `disp/003`-`disp/009` (57-87): `quadratic_lower`, `upper_envelope`, `breakpoint_value`,
  `calibration_recursion`, `scale_def`, `tie_difference`, `scale_bounds`.
* `disp/010`-`disp/013` (96-114): `step_notation`, `deficits_nonneg`, `pair_identities`,
  `secant_quotient`.
* `disp/014`-`disp/020` (123-152): `step_determinant`, `denominator_bounds`, `old_radial`,
  `radial_error`, `determinant_identity'`, `absorption_inequality`, `slope_determinant`.
* `disp/021`-`disp/025` (161-184): `quotient_multiplier`, `cancellation`,
  `multiplier_estimates`, `exponent_estimates`, `branch_change`.
* `disp/026`-`disp/032` (186-216): `normalized_arc`, `segment_affine`, `compensated_def`,
  `compensated_log`, `projected_transport`, `transport_loewner`.
* `disp/033`-`disp/038` (233-271): `example_objective`, `example_scale`, `printed_points`,
  `printed_metric`, `printed_identities`, `printed_radial`.
* `disp/039`-`disp/044` (275-313): `rho_choice`, `family_pair_def`, `family_identities`,
  `family_radial`, `printed_transported`, `printed_multiplier`.

Prose items are covered by the theorems whose docstrings cite them; the register lists every
name. The library proves (10.16) and the segment estimate of line 198 with one lemma on affine
functions instead of the adjacent/nonadjacent case analysis of the text; that case analysis is
`segment_cases`, on the segments of the arc.

## Non-vacuity

The `example`s at the end show that the standing assumptions can hold: an explicit admissible
run on $u^2+|v|$ (`absParabolaRun`, the library's `UnexcitedMetric.run`) for the theorem and
`mixed_in_family`; admissible runs on the example objective (10.18) (`example_run_exists`, from
the general existence theorem) for `example_flat_contour`, `example_applies` and
`converges_without_rs`; an explicit ordered pruned list of the example family with three pieces
(`examplePrunedOrder`) for the statements on consecutive pieces; eligible pairs of the example
family in the band $3\le F\le4$ with arbitrarily small $d$ for the band statements of the
visibility, denominator and transport paragraphs; and $u=A=\epsilon=1$, $c_1=1/4$, $c_2=1/2$ for
the example's pair statements.
-/

noncomputable section
open scoped Topology
open Set Filter Matrix BfgsVerification

namespace BfgsCoverage.Companion.Ch10Q

open Parabolic Parabolic.Family TransportedCertificate

/-! ### Helpers -/

/-- The finite parabolic maximum of the chapter, $F(u,v)=\max_i\{a_iu^2+b_iv\}$ written as
`IsGreatest` of the branch values, is the library's `Parabolic.Family.objective` of the family with
coefficients `a`, `b` (the structure fields `a_pos`, `negative_slope`, `positive_slope` are
$a_i>0$ and $\min_ib_i<0<\max_ib_i$). -/
theorem family_objective_eq {m : ℕ} (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (hneg : ∃ i, b i < 0) (hpos : ∃ i, 0 < b i) (F : Vec 2 → ℝ)
    (hF : ∀ x, IsGreatest (Set.range fun i => a i * (x 0) ^ 2 + b i * x 1) (F x)) :
    F = (⟨a, b, ha, hneg, hpos⟩ : Parabolic.Family m).objective := by
  funext x
  apply IsGreatest.unique (hF x)
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := (⟨a, b, ha, hneg, hpos⟩ : Parabolic.Family m).exists_active x
    exact ⟨i, hi.symm⟩
  · rintro _ ⟨i, rfl⟩
    exact (⟨a, b, ha, hneg, hpos⟩ : Parabolic.Family m).branch_le i x

/-- `P.objective x` is the greatest branch value: the library definition unfolds to the
displayed maximum. -/
theorem objective_isGreatest {m : ℕ} (P : Parabolic.Family m) (x : Vec 2) :
    IsGreatest (Set.range fun i => P.a i * (x 0) ^ 2 + P.b i * x 1) (P.objective x) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := P.exists_active x
    exact ⟨i, hi.symm⟩
  · rintro _ ⟨i, rfl⟩
    exact P.branch_le i x

/-! ### The theorem (`10_Q.tex:37-48`) -/

/-- Item `C/10_Q/theorem/001` (`companion/chapters/10_Q.tex:37-48`) ("Finite multi-branch
parabolic maxima"), with its displays `C/10_Q/disp/001` (lines 39-42) and `C/10_Q/disp/002`
(lines 44-46): "Let $m<\infty$ and
\[ F(u,v)=\max_{i\le m}\{a_iu^2+b_iv\},\qquad a_i>0,\quad\min_ib_i<0<\max_ib_i. \]
Every infinite admissible unmodified full-BFGS run, for arbitrary $H_0\succ0$ and fixed
$0<c_1<c_2<1$, satisfies $(u_k,v_k)\to(0,0)$, $F(u_k,v_k)\to0$."

$(u,v)$ is `x : Vec 2` with $u=x_0$, $v=x_1$; $H_0$, $c_1$, $c_2$ are fields of the run. The
remaining sentences of the theorem are `essential_branches_arbitrary` and `flat_branch_allowed`.
Proof: the library's `AdmissibleBFGSRun.parabolic_convergence` (a band certificate on every
positive band, `hasBandCertificates`, and the transported-certificate theorem). -/
theorem parabolic_convergence {m : ℕ} (a b : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (hneg : ∃ i, b i < 0) (hpos : ∃ i, 0 < b i) (F : Vec 2 → ℝ)
    (hF : ∀ x, IsGreatest (Set.range fun i => a i * (x 0) ^ 2 + b i * x 1) (F x))
    (R : AdmissibleBFGSRun 2 F) :
    Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 0) := by
  obtain rfl := family_objective_eq a b ha hneg hpos F hF
  obtain ⟨h1, h2⟩ := R.parabolic_convergence _
  exact ⟨h2, h1⟩

/-- Item `C/10_Q/theorem/001` (`companion/chapters/10_Q.tex:37-48`), sentence "The number of
essential branches is arbitrary." For every $N\ge2$ there is a family with $N$ branches all of
which are essential (each is the unique canonical maximizer of the normalized profile
$a_i+b_i\xi$ at some $\xi$): $a_i=N^2-t_i^2$, $b_i=2t_i$, $t_i=i-(N-1)/2$, the tangent lines of
$\xi\mapsto N^2+\xi^2$. ($N\ge2$ is forced: an admissible family has slopes of both signs.) -/
theorem essential_branches_arbitrary (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Parabolic.Family N, ∀ i, P.Essential i := by
  set t : Fin N → ℝ := fun i => (i : ℝ) - ((N : ℝ) - 1) / 2 with ht
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have htb : ∀ i : Fin N, |t i| < N := by
    intro i
    have hi : (i : ℝ) ≤ (N : ℝ) - 1 := by
      have := i.isLt
      have : (i : ℕ) + 1 ≤ N := this
      have : ((i : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast this
      linarith
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    rw [abs_lt]
    constructor <;> simp only [ht] <;> linarith
  have hinj : Function.Injective t := by
    intro i j h
    simp only [ht, sub_left_inj] at h
    exact Fin.ext (by exact_mod_cast h)
  let P : Parabolic.Family N :=
    { a := fun i => (N : ℝ) ^ 2 - t i ^ 2
      b := fun i => 2 * t i
      a_pos := fun i => by
        have h := htb i
        have h0 : 0 ≤ |t i| := abs_nonneg _
        have : t i ^ 2 < (N : ℝ) ^ 2 := by
          rw [← sq_abs]; exact pow_lt_pow_left₀ h h0 (by norm_num)
        linarith
      negative_slope := ⟨⟨0, by omega⟩, by simp only [ht]; norm_num; linarith⟩
      positive_slope := ⟨⟨N - 1, by omega⟩, by
        simp only [ht]
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith⟩ }
  refine ⟨P, fun i => ⟨fun j _ hb => ?_, t i, fun j _ hji => ?_⟩⟩
  · have : t j = t i := by
      have := hb
      simp only [P] at this
      linarith
    exact le_of_eq (hinj this).symm
  · simp only [Parabolic.Family.profile, P]
    have hne : t j ≠ t i := fun h => hji (hinj h)
    have hpos : 0 < (t j - t i) ^ 2 := by
      have := sub_ne_zero.mpr hne
      positivity
    nlinarith

/-- Item `C/10_Q/theorem/001` (`companion/chapters/10_Q.tex:37-48`), sentence "In particular,
branches with $b_i=0$, giving a region flat in the normal coordinate, are allowed." The family
of display \eqref{10.18}, $\max\{u^2+v,3u^2,2u^2-v\}$ (library `Parabolic.Example.family`),
satisfies the hypotheses of the theorem (it is a `Parabolic.Family`), has the branch $3u^2$ with
$b=0$, and on the open region $-u^2<v<2u^2$ it equals $3u^2$, with $v$-derivative $0$. -/
theorem flat_branch_allowed :
    Example.family.b 1 = 0 ∧
      (∀ x : Vec 2, -(x 0) ^ 2 < x 1 → x 1 < 2 * (x 0) ^ 2 →
        Example.family.objective x = 3 * (x 0) ^ 2 ∧
        HasFDerivAt Example.family.objective (gradientFunctional ![6 * x 0, 0]) x) := by
  refine ⟨rfl, fun x h1 h2 => ⟨Example.objective_middle_closed h1.le h2.le, ?_⟩⟩
  exact Example.middle_hasGradient h1 h2

/-- Item `C/10_Q/prose/001` (`companion/chapters/10_Q.tex:3`): "Flat contour segments are allowed
in this finite parabolic family. Its explicit field supplies a convergence theorem that is not
contained in the strict-contour planar result." The example family (a member of the family of
the theorem, so every run converges) has, at every positive level $t$, the vertical segment
$\{(\sqrt{t/3},v):-t/3\le v\le2t/3\}$ in its level set $\{F=t\}$ and on the boundary of the sublevel
$\{F\le t\}$, which is therefore not strictly convex: the strict-contour hypothesis of the
planar theorem (strictly convex positive sublevels, `09_C.tex:47`, also in its local form for
low sublevels) fails at every positive level, while the parabolic theorem applies. -/
theorem example_flat_contour :
    (∀ t : ℝ, 0 < t → ∀ v : ℝ, -(t / 3) ≤ v → v ≤ 2 * (t / 3) →
      Example.objective ![Real.sqrt (t / 3), v] = t ∧
        ![Real.sqrt (t / 3), v] ∈ frontier {x : Vec 2 | Example.objective x ≤ t}) ∧
      (∀ t : ℝ, 0 < t → ¬ StrictConvex ℝ {x : Vec 2 | Example.objective x ≤ t}) ∧
      (∀ R : AdmissibleBFGSRun 2 Example.objective,
        Tendsto (fun k => Example.objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) := by
  have hseg : ∀ t : ℝ, 0 < t → ∀ v : ℝ, -(t / 3) ≤ v → v ≤ 2 * (t / 3) →
      Example.objective ![Real.sqrt (t / 3), v] = t ∧
        ![Real.sqrt (t / 3), v] ∈ frontier {x : Vec 2 | Example.objective x ≤ t} := by
    intro t ht v h1 h2
    have hu2 : Real.sqrt (t / 3) ^ 2 = t / 3 := Real.sq_sqrt (by positivity)
    have hu0 : 0 ≤ Real.sqrt (t / 3) := Real.sqrt_nonneg _
    have hval : Example.objective ![Real.sqrt (t / 3), v] = t := by
      rw [Example.objective_middle_closed
        (by show -(Real.sqrt (t / 3)) ^ 2 ≤ v; rw [hu2]; exact h1)
        (by show v ≤ 2 * Real.sqrt (t / 3) ^ 2; rw [hu2]; exact h2)]
      show 3 * Real.sqrt (t / 3) ^ 2 = t
      rw [hu2]
      ring
    refine ⟨hval, subset_closure (show Example.objective ![Real.sqrt (t / 3), v] ≤ t from hval.le),
      fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    have hpt : (![Real.sqrt (t / 3) + ε / 2, v] : Vec 2) ∈
        Metric.ball (![Real.sqrt (t / 3), v] : Vec 2) ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      fin_cases i <;> simp [Real.dist_eq, abs_of_pos hε] <;> linarith
    have hle := hball hpt
    simp only [mem_setOf_eq] at hle
    have hq : 3 * (Real.sqrt (t / 3) + ε / 2) ^ 2 + 0 * v ≤
        Example.objective ![Real.sqrt (t / 3) + ε / 2, v] :=
      Example.family.branch_le 1 ![Real.sqrt (t / 3) + ε / 2, v]
    nlinarith [mul_nonneg hu0 hε.le, sq_pos_of_pos hε]
  refine ⟨hseg, fun t ht hsc => ?_, fun R => R.parabolic_convergence Example.family⟩
  obtain ⟨hv1, -⟩ := hseg t ht (-(t / 3)) le_rfl (by linarith)
  obtain ⟨hv2, -⟩ := hseg t ht (2 * (t / 3)) (by linarith) le_rfl
  obtain ⟨-, hfm⟩ := hseg t ht (t / 6) (by linarith) (by linarith)
  have hx : (![Real.sqrt (t / 3), -(t / 3)] : Vec 2) ∈ {x : Vec 2 | Example.objective x ≤ t} := by
    simp only [mem_setOf_eq]
    rw [hv1]
  have hy : (![Real.sqrt (t / 3), 2 * (t / 3)] : Vec 2) ∈
      {x : Vec 2 | Example.objective x ≤ t} := by
    simp only [mem_setOf_eq]
    rw [hv2]
  have hne : (![Real.sqrt (t / 3), -(t / 3)] : Vec 2) ≠ ![Real.sqrt (t / 3), 2 * (t / 3)] := by
    intro h
    have h1 : -(t / 3) = 2 * (t / 3) := congrFun h 1
    linarith
  have hmid := hsc hx hy hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have he : (1 / 2 : ℝ) • (![Real.sqrt (t / 3), -(t / 3)] : Vec 2) +
      (1 / 2 : ℝ) • ![Real.sqrt (t / 3), 2 * (t / 3)] = ![Real.sqrt (t / 3), t / 6] := by
    ext i
    fin_cases i
    · show 1 / 2 * Real.sqrt (t / 3) + 1 / 2 * Real.sqrt (t / 3) = Real.sqrt (t / 3)
      ring
    · show 1 / 2 * -(t / 3) + 1 / 2 * (2 * (t / 3)) = t / 6
      ring
  rw [he] at hmid
  exact hfm.2 hmid

/-! ### Compactness and the normalized upper envelope (`10_Q.tex:55-89`)

Standing assumptions: `P : Parabolic.Family m` (coefficients `P.a i > 0`, slopes `P.b i` of
both signs) and $F=$ `P.objective` (`objective_isGreatest`). -/

/-- Item `C/10_Q/prose/003` (`companion/chapters/10_Q.tex:56`): "Set $a_{\min}=\min_ia_i>0$."
The library's `minQuadratic` is the minimum of the $a_i$ (a lower bound attained by some $i$), and
it is positive. -/
theorem amin_def {m : ℕ} (P : Parabolic.Family m) :
    (∀ i, P.minQuadratic ≤ P.a i) ∧ (∃ i, P.minQuadratic = P.a i) ∧ 0 < P.minQuadratic := by
  refine ⟨P.minQuadratic_le, ?_, P.minQuadratic_pos⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' P.indices_nonempty P.a
  exact ⟨i, hi⟩

/-- Item `C/10_Q/disp/003` (`companion/chapters/10_Q.tex:57-59`), with the preceding claim (line
56) "A convex combination of one positive and one negative normal slope has slope zero, so
\[ F(u,v)\ge a_{\min}u^2." \]
Some convex combination $\lambda b_p+(1-\lambda)b_n$ of a positive and a negative slope is $0$, and
$F(u,v)\ge a_{\min}u^2$ for all $(u,v)$. -/
theorem quadratic_lower {m : ℕ} (P : Parabolic.Family m) :
    (∃ i j : Fin m, ∃ lam : ℝ, P.b i < 0 ∧ 0 < P.b j ∧ 0 ≤ lam ∧ lam ≤ 1 ∧
      lam * P.b j + (1 - lam) * P.b i = 0) ∧
      ∀ x : Vec 2, P.minQuadratic * (x 0) ^ 2 ≤ P.objective x := by
  obtain ⟨i, hi⟩ := P.negative_slope
  obtain ⟨j, hj⟩ := P.positive_slope
  have hd : P.b j - P.b i ≠ 0 := by linarith
  refine ⟨⟨i, j, -P.b i / (P.b j - P.b i), hi, hj, div_nonneg (by linarith) (by linarith),
    (div_le_one (by linarith)).mpr (by linarith), ?_⟩, P.quadratic_lower_bound P.minQuadratic_le⟩
  have he : -P.b i / (P.b j - P.b i) * P.b j + (1 - -P.b i / (P.b j - P.b i)) * P.b i =
      P.b i + -P.b i / (P.b j - P.b i) * (P.b j - P.b i) := by ring
  rw [he, div_mul_cancel₀ _ hd]
  ring

/-- Item `C/10_Q/prose/004` (`companion/chapters/10_Q.tex:60`): "The positive extreme slope bounds
$v$ above on a sublevel, and the negative extreme bounds it below. Thus every sublevel is
compact." On $\{F\le c\}$: $v\le c/b_j$ for a positive slope $b_j$, $v\ge c/b_i$ for a negative
slope $b_i$, $u^2\le c/a_{\min}$; and every sublevel is compact. -/
theorem sublevel_bounds {m : ℕ} (P : Parabolic.Family m) :
    (∀ (c : ℝ) (i j : Fin m), P.b i < 0 → 0 < P.b j → ∀ x : Vec 2, P.objective x ≤ c →
      x 1 ≤ c / P.b j ∧ c / P.b i ≤ x 1 ∧ (x 0) ^ 2 ≤ c / P.minQuadratic) ∧
      ∀ c : ℝ, IsCompact {x : Vec 2 | P.objective x ≤ c} := by
  refine ⟨fun c i j hi hj x hx => ⟨?_, ?_, ?_⟩, P.sublevel_compact⟩
  · have h := (P.branch_le j x).trans hx
    simp only [Parabolic.Family.branch] at h
    rw [le_div_iff₀ hj]
    nlinarith [mul_nonneg (P.a_pos j).le (sq_nonneg (x 0))]
  · have h := (P.branch_le i x).trans hx
    simp only [Parabolic.Family.branch] at h
    rw [div_le_iff_of_neg hi]
    nlinarith [mul_nonneg (P.a_pos i).le (sq_nonneg (x 0))]
  · rw [le_div_iff₀ P.minQuadratic_pos]
    have := (P.quadratic_lower_bound P.minQuadratic_le x).trans hx
    linarith

/-- Item `C/10_Q/prose/005` (`companion/chapters/10_Q.tex:60`): "At $u=0$, $F(0,v)>0$ for
$v\ne0$, proving uniqueness of the minimum zero." -/
theorem unique_minimum_zero {m : ℕ} (P : Parabolic.Family m) :
    (∀ v : ℝ, v ≠ 0 → 0 < P.objective ![0, v]) ∧ P.objective 0 = 0 ∧
      (∀ x, P.objective 0 ≤ P.objective x) ∧ (∀ x, P.objective x = 0 → x = 0) := by
  refine ⟨fun v hv => ?_, P.objective_zero, P.unique_minimum.1, P.unique_zero⟩
  rcases lt_or_gt_of_ne hv with h | h
  · obtain ⟨i, hi⟩ := P.negative_slope
    have := P.branch_le i ![0, v]
    simp only [Parabolic.Family.branch] at this
    simp at this
    nlinarith
  · obtain ⟨j, hj⟩ := P.positive_slope
    have := P.branch_le j ![0, v]
    simp only [Parabolic.Family.branch] at this
    simp at this
    nlinarith

/-- Item `C/10_Q/prose/006` (`companion/chapters/10_Q.tex:62`): "Discard globally redundant pieces,
merge equal normal slopes by retaining the largest $a_i$, and remove pieces active only on a tie.
Order the remaining pieces by strictly increasing $b_i$." The remaining pieces are the essential
ones (`Essential`: one canonical copy of each coefficient pair, strictly maximal among the
canonical pieces on an open interval of the normalized coordinate $\xi$, hence neither redundant
nor active only on a tie); an essential piece has the largest $a_i$ among the pieces with its
slope; the essential slopes are distinct and an order by strictly increasing slope exists
(`prunedOrder`); the pruned family has the same objective. -/
theorem pruning {m : ℕ} (P : Parabolic.Family m) :
    (∀ i, P.Essential i → ∀ j, P.b j = P.b i → P.a j ≤ P.a i) ∧
      (∀ i, P.Essential i → ∃ ξ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ Ioo (ξ - δ) (ξ + δ), ∀ j,
        P.Canonical j → j ≠ i → P.profile j ζ < P.profile i ζ) ∧
      (∀ i j, P.Essential i → P.Essential j → P.b i = P.b j → i = j) ∧
      (∃ O : P.PrunedOrder, StrictMono (fun k => P.b (O.index k)) ∧
        ∀ i, P.Essential i ↔ ∃ k, O.index k = i) ∧
      ∀ x, P.prunedFamily.objective x = P.objective x := by
  refine ⟨fun i hi j hj => P.essential_same_slope_maximal hi j hj,
    fun i hi => P.essential_strict_interval hi,
    fun i j hi hj hb => P.essential_slopes_injective hi hj hb,
    ⟨P.prunedOrder, P.prunedOrder.slopes_strictMono, fun i => ⟨P.prunedOrder.covers i, ?_⟩⟩,
    P.prunedFamily_objective⟩
  rintro ⟨k, rfl⟩
  exact P.prunedOrder.essential k

/-- Item `C/10_Q/disp/004` (`companion/chapters/10_Q.tex:63-65`): "They form the upper envelope
\[ \varphi(\xi)=\max_i(a_i+b_i\xi),\qquad \xi=v/u^2\quad(u\ne0). \]"
For an ordered list `O` of the remaining (essential) pieces and $\varphi$ (a variable) the maximum
of their profiles $a_i+b_i\xi$: $\varphi$ is also the maximum of all original profiles, and
$F(u,v)=u^2\varphi(v/u^2)$ for $u\ne0$. -/
theorem upper_envelope {m : ℕ} (P : Parabolic.Family m) (O : P.PrunedOrder) (φ : ℝ → ℝ)
    (hφ : ∀ ξ, IsGreatest (Set.range fun k => P.a (O.index k) + P.b (O.index k) * ξ) (φ ξ)) :
    (∀ ξ, IsGreatest (Set.range fun i => P.a i + P.b i * ξ) (φ ξ)) ∧
      ∀ x : Vec 2, x 0 ≠ 0 → P.objective x = (x 0) ^ 2 * φ (x 1 / (x 0) ^ 2) := by
  have hfull : ∀ ξ, IsGreatest (Set.range fun i => P.a i + P.b i * ξ) (φ ξ) := by
    intro ξ
    obtain ⟨i, hie, hia⟩ := P.exists_essential_profileActive ξ
    obtain ⟨k, rfl⟩ := O.covers i hie
    refine ⟨⟨O.index k, ?_⟩, ?_⟩
    · apply le_antisymm ((hφ ξ).2 ⟨k, rfl⟩)
      obtain ⟨l, hl⟩ := (hφ ξ).1
      rw [← hl]
      exact hia (O.index l)
    · rintro _ ⟨j, rfl⟩
      exact (hia j).trans ((hφ ξ).2 ⟨k, rfl⟩)
  refine ⟨hfull, fun x hx => ?_⟩
  have hu : 0 < (x 0) ^ 2 := by positivity
  apply IsGreatest.unique (objective_isGreatest P x)
  have hg := hfull (x 1 / (x 0) ^ 2)
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hg.1
    refine ⟨i, ?_⟩
    simp only at hi ⊢
    rw [← hi]
    field_simp
  · rintro _ ⟨i, rfl⟩
    have := hg.2 ⟨i, rfl⟩
    simp only at this ⊢
    have h2 := mul_le_mul_of_nonneg_left this hu.le
    calc P.a i * (x 0) ^ 2 + P.b i * x 1 = (x 0) ^ 2 * (P.a i + P.b i * (x 1 / (x 0) ^ 2)) := by
          field_simp
      _ ≤ _ := h2

/-- Item `C/10_Q/prose/007` (`companion/chapters/10_Q.tex:66`): "The neighboring breakpoints
$\xi_i$ increase strictly." For consecutive pieces of the ordered pruned list, the breakpoint
$\xi_k$ (where pieces $k$ and $k+1$ tie, `breakpoint`) is strictly smaller than $\xi_{k+1}$. -/
theorem breakpoints_increasing {m : ℕ} (P : Parabolic.Family m) (O : P.PrunedOrder)
    {i j k : Fin O.count} (hij : j.val = i.val + 1) (hjk : k.val = j.val + 1) :
    P.breakpoint (O.index i) (O.index j) < P.breakpoint (O.index j) (O.index k) :=
  O.consecutive_breakpoints_increasing P hij hjk

/-- Item `C/10_Q/disp/005` (`companion/chapters/10_Q.tex:67-69`): "Put
\[ A_i=a_i+b_i\xi_i=a_{i+1}+b_{i+1}\xi_i>0." \]
For consecutive pieces $p=\sigma(k)$, $q=\sigma(k+1)$ of the ordered pruned list, with
$\xi=(a_p-a_q)/(b_q-b_p)$ their breakpoint and $A$ a variable with its defining equation: the
two profiles agree at $\xi$, both are maximal there, and $A>0$. -/
theorem breakpoint_value {m : ℕ} (P : Parabolic.Family m) (O : P.PrunedOrder)
    {i j : Fin O.count} (hij : j.val = i.val + 1) (ξ : ℝ)
    (hξ : ξ = P.breakpoint (O.index i) (O.index j)) (A : ℝ)
    (hA : A = P.a (O.index i) + P.b (O.index i) * ξ) :
    A = P.a (O.index j) + P.b (O.index j) * ξ ∧ 0 < A ∧
      P.ProfileActive (O.index i) ξ ∧ P.ProfileActive (O.index j) ξ := by
  have hadj := O.adjacent P hij
  have hb : P.b (O.index i) < P.b (O.index j) := hadj.2.2.1
  have he := P.breakpoint_profile_eq hb
  have hpos := P.adjacent_breakpoint_value_pos hadj
  obtain ⟨h1, h2⟩ := P.adjacent_breakpoint_active hadj
  subst hξ hA
  exact ⟨he, hpos, h1, h2⟩

/-- Item `C/10_Q/disp/006`, equation (10.7) (`companion/chapters/10_Q.tex:71-73`): "Choose
constants $k_i$ recursively:
\[ k_{i+1}-k_i=-\frac{a_{i+1}-a_i}{2A_i}." \]
The library's constants `calibration` (defined for every original index) satisfy the recursion for
consecutive pieces of the ordered pruned list; any other solution differs from them by a constant
along the list (the recursion fixes all differences). -/
theorem calibration_recursion {m : ℕ} (P : Parabolic.Family m) (O : P.PrunedOrder)
    {i j : Fin O.count} (hij : j.val = i.val + 1) (A : ℝ)
    (hA : A = P.a (O.index i) + P.b (O.index i) * P.breakpoint (O.index i) (O.index j)) :
    P.calibration (O.index j) - P.calibration (O.index i) =
      -(P.a (O.index j) - P.a (O.index i)) / (2 * A) := by
  rw [hA]
  exact P.adjacent_calibration (O.adjacent P hij)

/-- Item `C/10_Q/disp/007`, equation (10.8) (`companion/chapters/10_Q.tex:75-79`): "At a
differentiable point with active branch $i$, define
\[ r(u,v)=(u,2v)^T,\qquad \theta(u,v)=\exp\left\{\frac{a_iu^2}{2F(u,v)}+k_i\right\},\qquad
   W=\theta^2rr^T." \]
The library's `radialDirection`, `calibratedScale` and `calibratedVector` $=\theta r$: $r$ is
literally $(u,2v)$; at every point with $F>0$ and every active branch $i$, $\theta$ is the displayed
exponential with $k_i=$ `calibration i`; and $W=\theta^2rr^T$ is `outer (calibratedVector x)
(calibratedVector x)`, the field of the certificate (`exists_bandCertificate`). -/
theorem scale_def {m : ℕ} (P : Parabolic.Family m) (x : Vec 2) :
    radialDirection x = ![x 0, 2 * x 1] ∧
      (∀ i, P.Active i x → 0 < P.objective x →
        P.calibratedScale x =
          Real.exp (P.a i * (x 0) ^ 2 / (2 * P.objective x) + P.calibration i)) ∧
      outer (P.calibratedVector x) (P.calibratedVector x) =
        (P.calibratedScale x) ^ 2 • outer (radialDirection x) (radialDirection x) := by
  refine ⟨rfl, fun i hi hx => P.calibratedScale_eq_active hi hx, ?_⟩
  ext k l
  simp only [Parabolic.Family.calibratedVector, outer, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  ring

/-- Item `C/10_Q/prose/008` (`companion/chapters/10_Q.tex:80`): "The constants make $\theta$ agree
across every switching interface." At every point with $F>0$, any two active branches give the
same exponent $a_iu^2/(2F)+k_i$ (library `calibration_active_eq`, valid for every pair of active
branches, adjacent or not). -/
theorem scale_interfaces {m : ℕ} (P : Parabolic.Family m) {i j : Fin m} {x : Vec 2}
    (hi : P.Active i x) (hj : P.Active j x) (hx : 0 < P.objective x) :
    P.a i * (x 0) ^ 2 / (2 * P.objective x) + P.calibration i =
      P.a j * (x 0) ^ 2 / (2 * P.objective x) + P.calibration j :=
  P.calibration_active_eq hi hj hx

/-- Item `C/10_Q/disp/008` (`companion/chapters/10_Q.tex:81-83`): "At a tie $v=\xi_iu^2$ the
exponent difference is
\[ \frac{a_{i+1}-a_i}{2A_i}+k_{i+1}-k_i=0." \]
For consecutive pieces $p=\sigma(k)$, $q=\sigma(k+1)$ with breakpoint $\xi$, $A$ as in display
`disp/005`, and every $u\ne0$: at $x=(u,\xi u^2)$ both pieces are active, $F(x)=Au^2$, the exponent
difference $(a_qu^2/(2F)+k_q)-(a_pu^2/(2F)+k_p)$ equals $(a_q-a_p)/(2A)+k_q-k_p$, and it is $0$. -/
theorem tie_difference {m : ℕ} (P : Parabolic.Family m) (O : P.PrunedOrder)
    {i j : Fin O.count} (hij : j.val = i.val + 1) (ξ : ℝ)
    (hξ : ξ = P.breakpoint (O.index i) (O.index j)) (A : ℝ)
    (hA : A = P.a (O.index i) + P.b (O.index i) * ξ) (u : ℝ) (hu : u ≠ 0) :
    P.Active (O.index i) ![u, ξ * u ^ 2] ∧ P.Active (O.index j) ![u, ξ * u ^ 2] ∧
      P.objective ![u, ξ * u ^ 2] = A * u ^ 2 ∧
      (P.a (O.index j) * u ^ 2 / (2 * P.objective ![u, ξ * u ^ 2]) + P.calibration (O.index j)) -
          (P.a (O.index i) * u ^ 2 / (2 * P.objective ![u, ξ * u ^ 2]) +
            P.calibration (O.index i)) =
        (P.a (O.index j) - P.a (O.index i)) / (2 * A) + P.calibration (O.index j) -
          P.calibration (O.index i) ∧
      (P.a (O.index j) - P.a (O.index i)) / (2 * A) + P.calibration (O.index j) -
          P.calibration (O.index i) = 0 := by
  obtain ⟨hAj, hApos, hpi, hpj⟩ := breakpoint_value P O hij ξ hξ A hA
  have hrec := calibration_recursion P O hij A (by rw [hA, hξ])
  have hu2 : 0 < u ^ 2 := by positivity
  -- profile activity at ξ scales to activity at (u, ξu²)
  have hact : ∀ p : Fin m, P.ProfileActive p ξ → P.Active p ![u, ξ * u ^ 2] := by
    intro p hp
    apply le_antisymm
    · apply Finset.sup'_le
      intro q _
      have := mul_le_mul_of_nonneg_left (hp q) hu2.le
      simp only [Parabolic.Family.branch, Parabolic.Family.profile, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] at this ⊢
      nlinarith
    · exact P.branch_le p _
  have hai := hact _ hpi
  have haj := hact _ hpj
  have hval : P.objective ![u, ξ * u ^ 2] = A * u ^ 2 := by
    rw [hai]
    simp only [Parabolic.Family.branch, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hA]
    ring
  have hA0 : A ≠ 0 := hApos.ne'
  refine ⟨hai, haj, hval, ?_, ?_⟩
  · rw [hval]
    field_simp
    ring
  · have he : (P.a (O.index j) - P.a (O.index i)) / (2 * A) =
        -(-(P.a (O.index j) - P.a (O.index i)) / (2 * A)) := by ring
    linarith

/-- Item `C/10_Q/prose/009` (`companion/chapters/10_Q.tex:84`): "The field is well-defined on
$F>0$, including by continuous extension across ties." $\theta$ does not depend on the choice of
active branch (`scale_interfaces`) and $\theta$, $\theta r$ and $W=\theta^2rr^T$ are continuous on
$\{F>0\}$, including at every switching interface. -/
theorem scale_continuous {m : ℕ} (P : Parabolic.Family m) :
    ContinuousOn P.calibratedScale {x | 0 < P.objective x} ∧
      ContinuousOn P.calibratedVector {x | 0 < P.objective x} ∧
      ContinuousOn (fun x => outer (P.calibratedVector x) (P.calibratedVector x))
        {x | 0 < P.objective x} :=
  ⟨P.calibratedScale_continuousOn, P.calibratedVector_continuousOn,
    P.certificateField_continuousOn⟩

/-- Item `C/10_Q/disp/009` (`companion/chapters/10_Q.tex:85-87`), with the preceding claim of line
84: "Since $0\le u^2/F\le1/a_{\min}$, there are global constants
\[ 0<\theta_{\min}\le\theta\le\theta_{\max}<\infty." \]
On $\{F>0\}$. -/
theorem scale_bounds {m : ℕ} (P : Parabolic.Family m) :
    (∀ x : Vec 2, 0 < P.objective x →
      0 ≤ (x 0) ^ 2 / P.objective x ∧ (x 0) ^ 2 / P.objective x ≤ 1 / P.minQuadratic) ∧
      ∃ θmin θmax : ℝ, 0 < θmin ∧ θmin ≤ θmax ∧
        ∀ x : Vec 2, 0 < P.objective x →
          θmin ≤ P.calibratedScale x ∧ P.calibratedScale x ≤ θmax := by
  refine ⟨fun x hx => ⟨div_nonneg (sq_nonneg _) hx.le, ?_⟩, ?_⟩
  · rw [div_le_div_iff₀ hx P.minQuadratic_pos, one_mul]
    have := P.quadratic_lower_bound P.minQuadratic_le x
    linarith
  · obtain ⟨θlo, θhi, hlo, hhi, hb⟩ := P.calibratedScale_uniform_bounds
    refine ⟨θlo, max θlo θhi, hlo, le_max_left _ _, fun x hx => ⟨(hb x hx).1, ?_⟩⟩
    exact (hb x hx).2.trans (le_max_right _ _)

/-! ### Visibility and secant correction (`10_Q.tex:94-116`)

Standing assumptions (line 95): a compact positive band $\eta\le F\le B$ ($\eta>0$), points
$x=(u,v)$ and $z=(u',v')$ of the band with gradients $g=\nabla F(x)$, $g'=\nabla F(z)$
(the TeX's $y=g'-g$), an active ("old") branch $i$ at $x$ and an active ("new") branch $j$ at
$z$. $d=-g^Ts$, $\Delta=F(x)-F(z)$, $t=y^Ts$ are `pairDecrease`, written out, `pairCurvature`
(the notation of `01_I.tex:137`). -/

/-- The band $\{\eta\le F\le B\}$ is compact. -/
theorem band_compact {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) :
    IsCompact {x : Vec 2 | η ≤ P.objective x ∧ P.objective x ≤ B} := by
  apply (P.sublevel_compact B).of_isClosed_subset
  · exact (isClosed_le continuous_const P.objective_continuous).inter
      (isClosed_le P.objective_continuous continuous_const)
  · intro x hx; exact hx.2

/-- Item `C/10_Q/disp/010` (`companion/chapters/10_Q.tex:96-98`): the notation
\[ h=u'-u,\quad \ell=v'-v,\quad s=(h,\ell), \]
the library's `horizontalStep x z`, `normalStep x z` and `pairStep x z` $=z-x$. -/
theorem step_notation (x z : Vec 2) :
    horizontalStep x z = z 0 - x 0 ∧ normalStep x z = z 1 - x 1 ∧
      pairStep x z = ![horizontalStep x z, normalStep x z] := by
  refine ⟨rfl, rfl, ?_⟩
  ext k; fin_cases k <;> rfl

/-- Item `C/10_Q/disp/011` (`companion/chapters/10_Q.tex:99-102`):
\[ e=F(z)-(a_iu'^2+b_iv')\ge0,\qquad \bar e=F(x)-(a_ju^2+b_jv)\ge0. \]
$e$, $\bar e$ are variables with their defining equations (the library's `deficit i z`,
`deficit j x`); nonnegativity holds for all branches and points. -/
theorem deficits_nonneg {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (_hη : 0 < η) (x z : Vec 2)
    (_hx : η ≤ P.objective x ∧ P.objective x ≤ B) (_hz : η ≤ P.objective z ∧ P.objective z ≤ B)
    (i j : Fin m) (_hi : P.Active i x) (_hj : P.Active j z)
    (e ebar : ℝ) (he : e = P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1))
    (hebar : ebar = P.objective x - (P.a j * (x 0) ^ 2 + P.b j * x 1)) :
    0 ≤ e ∧ 0 ≤ ebar ∧ e = P.deficit i z ∧ ebar = P.deficit j x := by
  have h1 : e = P.deficit i z := by rw [he]; rfl
  have h2 : ebar = P.deficit j x := by rw [hebar]; rfl
  exact ⟨h1 ▸ P.deficit_nonneg i z, h2 ▸ P.deficit_nonneg j x, h1, h2⟩

/-- Item `C/10_Q/disp/012`, equations (10.9)-(10.12) (`companion/chapters/10_Q.tex:104-109`):
"Exact identities are
\[ d-\Delta=a_ih^2+e,\quad t=(a_i+a_j)h^2+e+\bar e,\quad g^Tr(x)=2F(x),\quad
   y^Tr(z)=2a_ihu'+2e." \]
Under the standing assumptions, with $h$, $e$, $\bar e$ variables with their defining
equations, $r=$ `radialDirection` $=(u,2v)$. -/
theorem pair_identities {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (_hη : 0 < η) (x z : Vec 2)
    (_hx : η ≤ P.objective x ∧ P.objective x ≤ B) (_hz : η ≤ P.objective z ∧ P.objective z ≤ B)
    (g g' : Vec 2) (hg : HasFDerivAt P.objective (gradientFunctional g) x)
    (hg' : HasFDerivAt P.objective (gradientFunctional g') z)
    (i j : Fin m) (hi : P.Active i x) (hj : P.Active j z)
    (h : ℝ) (hh : h = z 0 - x 0)
    (e ebar : ℝ) (he : e = P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1))
    (hebar : ebar = P.objective x - (P.a j * (x 0) ^ 2 + P.b j * x 1)) :
    pairDecrease x z g - (P.objective x - P.objective z) = P.a i * h ^ 2 + e ∧
      pairCurvature x z g g' = (P.a i + P.a j) * h ^ 2 + e + ebar ∧
      dot g (radialDirection x) = 2 * P.objective x ∧
      dot (g' - g) (radialDirection z) = 2 * P.a i * h * z 0 + 2 * e := by
  have hgi := P.active_eq_gradient hi hg
  have hgj := P.active_eq_gradient hj hg'
  have he' : e = P.deficit i z := by rw [he]; rfl
  have hebar' : ebar = P.deficit j x := by rw [hebar]; rfl
  have hh' : h = horizontalStep x z := hh
  subst hgi hgj
  rw [he', hebar', hh']
  exact ⟨P.decrease_gap_identity hi, P.curvature_identity hi hj, P.visibility_identity hi,
    P.secant_radial_identity hj⟩

/-- Item `C/10_Q/prose/013` (`companion/chapters/10_Q.tex:110`): "For eligible pairs,
$h^2\le d/a_{\min}$ and $e\le d$." Under the standing assumptions, for an eligible pair
(`EligiblePair P.objective c₁ c₂ x z g g'`, with $0\le c_1$). -/
theorem eligible_step_bounds {m : ℕ} (P : Parabolic.Family m) (x z : Vec 2) (g g' : Vec 2)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hp : EligiblePair P.objective c₁ c₂ x z g g')
    (i : Fin m) (hi : P.Active i x) :
    (z 0 - x 0) ^ 2 ≤ pairDecrease x z g / P.minQuadratic ∧
      P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1) ≤ pairDecrease x z g :=
  ⟨P.eligible_horizontal_sq_le hc₁ hi hp, P.eligible_deficit_le hc₁ hi hp⟩

/-- Item `C/10_Q/disp/013` (`companion/chapters/10_Q.tex:111-114`): "Weighted Cauchy--Schwarz
gives
\[ \frac{(y^Tr(z))^2}{t}\le\frac{4a_i^2}{a_i+a_j}u'^2+4e." \]
Under the standing assumptions, for $t>0$ (eligible pairs have $t\ge(1-c_2)d>0$); $e$ as in
display `disp/011`. -/
theorem secant_quotient {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (_hη : 0 < η) (x z : Vec 2)
    (_hx : η ≤ P.objective x ∧ P.objective x ≤ B) (_hz : η ≤ P.objective z ∧ P.objective z ≤ B)
    (g g' : Vec 2) (hg : HasFDerivAt P.objective (gradientFunctional g) x)
    (hg' : HasFDerivAt P.objective (gradientFunctional g') z)
    (i j : Fin m) (hi : P.Active i x) (hj : P.Active j z)
    (e : ℝ) (he : e = P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1))
    (ht : 0 < pairCurvature x z g g') :
    dot (g' - g) (radialDirection z) ^ 2 / pairCurvature x z g g' ≤
      4 * (P.a i) ^ 2 / (P.a i + P.a j) * (z 0) ^ 2 + 4 * e := by
  have hgi := P.active_eq_gradient hi hg
  have hgj := P.active_eq_gradient hj hg'
  have he' : e = P.deficit i z := by rw [he]; rfl
  subst hgi hgj
  rw [he']
  exact P.secant_quotient_bound hi hj ht

/-- $y^TWy=(y^T\theta r)^2$ for the rank-one field $W=(\theta r)(\theta r)^T$. -/
theorem rankOne_energy (w y : Vec 2) : dot y (outer w w *ᵥ y) = (dot y w) ^ 2 := by
  simp [dot, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Item `C/10_Q/prose/014` (`companion/chapters/10_Q.tex:115`): "The right side is uniformly
bounded on the compact band for small $d$. Multiplication by $\theta(z)^2$ proves (S) of
Chapter~\ref{comp:T}. Equation (10.11) proves (V) with $m=4\theta_{\min}^2\eta^2$." Corrected on
15 October 2026 (M28: "Equation (11)" printed a number that no companion equation has; W26: "(S)
of Chapter~\ref{comp:T}"). On the band $K=\{\eta\le F\le B\}$, with
$0\le c_1$, $c_2<1$: some $C$ bounds the right side of display `disp/013` over eligible pairs with
$d\le1$; some $C'$ gives (S) $y^TW(z)y=(y^T\theta(z)r(z))^2\le C't$ for those pairs; and (V)
$g^TW(x)g=(g^T\theta(x)r(x))^2\ge4\theta_{\min}^2\eta^2$ at every differentiable point of the band,
with $\theta_{\min}$ any lower bound of $\theta$ on $F>0$ (display `disp/009`). -/
theorem secant_visibility {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (hη : 0 < η)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    (∃ C : ℝ, ∀ x z g g' i j, η ≤ P.objective x ∧ P.objective x ≤ B →
      η ≤ P.objective z ∧ P.objective z ≤ B → EligiblePair P.objective c₁ c₂ x z g g' →
      P.Active i x → P.Active j z → pairDecrease x z g ≤ 1 →
      4 * (P.a i) ^ 2 / (P.a i + P.a j) * (z 0) ^ 2 +
        4 * (P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1)) ≤ C) ∧
    (∃ C' : ℝ, ∀ x z g g', η ≤ P.objective x ∧ P.objective x ≤ B →
      η ≤ P.objective z ∧ P.objective z ≤ B → EligiblePair P.objective c₁ c₂ x z g g' →
      pairDecrease x z g ≤ 1 →
      dot (g' - g) (outer (P.calibratedVector z) (P.calibratedVector z) *ᵥ (g' - g)) ≤
        C' * pairCurvature x z g g') ∧
    ∀ θmin : ℝ, 0 ≤ θmin → (∀ x, 0 < P.objective x → θmin ≤ P.calibratedScale x) →
      ∀ x g, η ≤ P.objective x → HasFDerivAt P.objective (gradientFunctional g) x →
        4 * θmin ^ 2 * η ^ 2 ≤
          dot g (outer (P.calibratedVector x) (P.calibratedVector x) *ᵥ g) := by
  have hK := band_compact P η B
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨R, hR, hrad⟩ := compact_sqNorm_radius hK (0 : Vec 2)
    refine ⟨4 * P.maxQuadratic * R ^ 2 + 4, fun x z g g' i j hx hz hp hi hj hd => ?_⟩
    have hz0 : (z 0) ^ 2 ≤ R ^ 2 := by
      have := hrad z hz
      rw [sub_zero] at this
      have h0 : (z 0) ^ 2 ≤ sqNorm z := by
        simp only [sqNorm, Fin.sum_univ_two]; nlinarith [sq_nonneg (z 1)]
      linarith
    have hcoef : 4 * (P.a i) ^ 2 / (P.a i + P.a j) ≤ 4 * P.maxQuadratic := by
      have hai := P.a_pos i
      have haj := P.a_pos j
      rw [div_le_iff₀ (by linarith)]
      have := P.le_maxQuadratic i
      nlinarith
    have he := P.eligible_deficit_le hc₁ hi hp
    have he' : P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1) ≤ 1 := by
      change P.deficit i z ≤ 1; linarith
    have h1 := mul_le_mul hcoef hz0 (sq_nonneg _) (by have := P.maxQuadratic_pos; positivity)
    nlinarith
  · obtain ⟨C, hC, hsec⟩ := P.exists_uniform_secant_bound hK hc₁ hc₂
    obtain ⟨θlo, θhi, hlo, hhi, hscale⟩ := P.calibratedScale_uniform_bounds
    refine ⟨θhi ^ 2 * C, fun x z g g' hx hz hp hd => ?_⟩
    rw [rankOne_energy, Parabolic.Family.calibratedVector, dot_smul_right, mul_pow]
    have hb := hsec x hx z hz g g' hp hd
    have hFz : 0 < P.objective z := hη.trans_le hz.1
    have hup := (hscale z hFz).2
    have hsq : (P.calibratedScale z) ^ 2 ≤ θhi ^ 2 := by
      nlinarith [P.calibratedScale_pos z]
    calc P.calibratedScale z ^ 2 * dot (g' - g) (radialDirection z) ^ 2
        ≤ θhi ^ 2 * (C * pairCurvature x z g g') :=
          mul_le_mul hsq hb (sq_nonneg _) (sq_nonneg _)
      _ = θhi ^ 2 * C * pairCurvature x z g g' := by ring
  · intro θmin hθ0 hθ x g hx hg
    rw [rankOne_energy, Parabolic.Family.calibratedVector, dot_smul_right, mul_pow]
    have hvis := P.positive_visibility hη.le hx hg
    have hlow := hθ x (hη.trans_le hx)
    have hsq : θmin ^ 2 ≤ (P.calibratedScale x) ^ 2 := by nlinarith
    have := mul_le_mul hsq hvis (by positivity) (sq_nonneg _)
    linarith

/-! ### The step quotient on small-decrease pairs (`10_Q.tex:121-154`) -/

/-- Item `C/10_Q/disp/014` (`companion/chapters/10_Q.tex:123-125`): "Define
\[ D=\det(s,r(x))=2vh-u\ell." \]
The library's `stepDeterminant x z` is $2vh-u\ell$, and it equals the determinant of the columns
$s$, $r(x)$ (`determinant v w` $=v_0w_1-v_1w_0$). -/
theorem step_determinant (x z : Vec 2) :
    stepDeterminant x z = 2 * x 1 * horizontalStep x z - x 0 * normalStep x z ∧
      determinant (pairStep x z) (radialDirection x) = stepDeterminant x z := by
  refine ⟨rfl, ?_⟩
  simp only [determinant, pairStep, radialDirection, stepDeterminant, horizontalStep, normalStep,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.sub_apply]
  ring

/-- Item `C/10_Q/disp/015`, equation (10.13) (`companion/chapters/10_Q.tex:127-129`): "We next
prove, uniformly on the positive band and for sufficiently small eligible $d$,
\[ d\le C|D|,\qquad |h|\le C|D|." \]
On the band $K=\{\eta\le F\le B\}$ ($\eta>0$, $0\le c_1$, $c_2<1$): some $C>0$ and $\delta>0$ give,
for every eligible pair in $K$ with $d\le\delta$, both bounds and $D\ne0$ (lines 149-153; library
`exists_small_denominator_bounds`). -/
theorem denominator_bounds {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (hη : 0 < η)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ x z g g' : Vec 2,
      η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
      EligiblePair P.objective c₁ c₂ x z g g' → pairDecrease x z g ≤ δ →
      pairDecrease x z g ≤ C * |stepDeterminant x z| ∧
        |horizontalStep x z| ≤ C * |stepDeterminant x z| ∧ stepDeterminant x z ≠ 0 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := P.exists_small_denominator_bounds (band_compact P η B) hη hc₁ hc₂
  exact ⟨C, δ, hC, hδ, fun x z g g' hx hz hp hd => hb x hx z hz g g' hp hx.1 hd⟩

/-- Item `C/10_Q/prose/016` (`companion/chapters/10_Q.tex:132`): "Let $N=y^Tr(z)$. Since
$r(z)-r(x)=\operatorname{diag}(1,2)s$". ($N$ only names $y^Tr(z)$.) -/
theorem radial_difference (x z : Vec 2) :
    radialDirection z - radialDirection x = !![1, 0; 0, 2] *ᵥ pairStep x z := by
  ext k
  fin_cases k
  all_goals simp [radialDirection, pairStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- Item `C/10_Q/disp/016` (`companion/chapters/10_Q.tex:133-135`):
\[ y^Tr(x)=-2t+N+y_uh, \]
with $N=y^Tr(z)$ and $y_u$ the first component of $y$; for all points and vectors. -/
theorem old_radial (x z y : Vec 2) (N : ℝ) (hN : N = dot y (radialDirection z)) :
    dot y (radialDirection x) = -2 * dot y (pairStep x z) + N + y 0 * horizontalStep x z := by
  rw [hN]
  simp [dot, radialDirection, pairStep, horizontalStep, Fin.sum_univ_two]
  ring

/-- Gradients and first coordinates are bounded on the band. -/
theorem band_bounds {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) :
    ∃ G R : ℝ, 0 < G ∧ 0 < R ∧ ∀ x ∈ {x : Vec 2 | η ≤ P.objective x ∧ P.objective x ≤ B},
      |x 0| ≤ R ∧ ∀ g, HasFDerivAt P.objective (gradientFunctional g) x → ∀ k, |g k| ≤ G := by
  have hK := band_compact P η B
  obtain ⟨R, hR, hrad⟩ := compact_sqNorm_radius hK (0 : Vec 2)
  obtain ⟨G, hG, hgrad⟩ := convex_supporting_bound_on_compact P.objective_convex hK
  refine ⟨G, R, hG, hR, fun x hx => ⟨?_, fun g hg k => ?_⟩⟩
  · exact abs_coordinate_of_sqNorm_le hR.le (by simpa only [sub_zero] using hrad x hx) 0
  · exact abs_coordinate_of_sqNorm_le hG.le
      (hgrad x hx g (convex_supporting_inequality P.objective_convex hg)) k

/-- Item `C/10_Q/disp/017` (`companion/chapters/10_Q.tex:137-139`), with the claim of line 136:
"By (10.12), bounded endpoints and gradients, and $e\le d$,
\[ y^Tr(x)=-2t+\varepsilon,\qquad |\varepsilon|\le C(|h|+d)." \]
On the band $K$ ($0\le c_1$): some $C\ge0$ gives $|y^Tr(x)+2t|\le C(|h|+d)$ for every eligible
pair in $K$ ($\varepsilon$ is $y^Tr(x)+2t$). -/
theorem radial_error {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z g g' : Vec 2,
      η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
      EligiblePair P.objective c₁ c₂ x z g g' →
      |dot (g' - g) (radialDirection x) + 2 * pairCurvature x z g g'| ≤
        C * (|horizontalStep x z| + pairDecrease x z g) := by
  obtain ⟨G, R, hG, hR, hb⟩ := band_bounds P η B
  refine ⟨2 * P.maxQuadratic * R + 2 * G + 2, by have := P.maxQuadratic_pos; positivity,
    fun x z g g' hx hz hp => ?_⟩
  obtain ⟨i, hi, hgi⟩ := P.gradient_from_active hp.gradient_x
  obtain ⟨j, hj, hgj⟩ := P.gradient_from_active hp.gradient_z
  have hold := P.old_radial_identity (i := i) (x := x) hj
  rw [← hgi, ← hgj] at hold
  have hd := hp.decrease_pos
  have he : P.deficit i z ≤ pairDecrease x z g := P.eligible_deficit_le hc₁ hi hp
  have herr := P.radial_error_bound hG.le hR.le hd.le (hb z hz).1
    (by rw [← hgi]; exact (hb x hx).2 g hp.gradient_x 0)
    (by rw [← hgj]; exact (hb z hz).2 g' hp.gradient_z 0) he
  rw [← hgi, ← hgj] at herr
  rw [hold]
  have : -2 * pairCurvature x z g g' + (2 * P.a i * horizontalStep x z * z 0 +
      2 * P.deficit i z + (g' 0 - g 0) * horizontalStep x z) + 2 * pairCurvature x z g g' =
      2 * P.a i * horizontalStep x z * z 0 + 2 * P.deficit i z +
        (g' 0 - g 0) * horizontalStep x z := by ring
  rw [this]
  exact herr

/-- Item `C/10_Q/disp/018` (`companion/chapters/10_Q.tex:141-144`): "The two-dimensional
determinant identity yields
\[ \det(g,y)D=(g^Ts)(y^Tr(x))-(g^Tr(x))(y^Ts)=-d\,y^Tr(x)-2F(x)t." \]
For a differentiable $x$ with gradient $g$, any $z$ and $y$ (here $y=g'-g$ for a gradient $g'$ at
$z$). -/
theorem determinant_identity' {m : ℕ} (P : Parabolic.Family m) (x z g g' : Vec 2)
    (hg : HasFDerivAt P.objective (gradientFunctional g) x) :
    determinant g (g' - g) * stepDeterminant x z =
        dot g (pairStep x z) * dot (g' - g) (radialDirection x) -
          dot g (radialDirection x) * dot (g' - g) (pairStep x z) ∧
      dot g (pairStep x z) * dot (g' - g) (radialDirection x) -
          dot g (radialDirection x) * dot (g' - g) (pairStep x z) =
        -pairDecrease x z g * dot (g' - g) (radialDirection x) -
          2 * P.objective x * pairCurvature x z g g' := by
  obtain ⟨i, hi, hgi⟩ := P.gradient_from_active hg
  have h := determinant_dot_identity g (g' - g) (pairStep x z) (radialDirection x)
  rw [(step_determinant x z).2] at h
  refine ⟨h, ?_⟩
  have hv : dot g (radialDirection x) = 2 * P.objective x := by
    rw [hgi]; exact P.visibility_identity hi
  rw [hv]
  simp only [pairDecrease, pairCurvature, neg_neg]

/-- Item `C/10_Q/disp/019` (`companion/chapters/10_Q.tex:146-148`): "Consequently
\[ (2F(x)-2d)t\le C|D|+Cd(|h|+d)." \]
On the band $K$ ($0\le c_1$): some $C$ works for every eligible pair in $K$. -/
theorem absorption_inequality {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (c₁ c₂ : ℝ)
    (hc₁ : 0 ≤ c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z g g' : Vec 2,
      η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
      EligiblePair P.objective c₁ c₂ x z g g' →
      (2 * P.objective x - 2 * pairDecrease x z g) * pairCurvature x z g g' ≤
        C * |stepDeterminant x z| +
          C * pairDecrease x z g * (|horizontalStep x z| + pairDecrease x z g) := by
  obtain ⟨G, R, hG, hR, hb⟩ := band_bounds P η B
  obtain ⟨E, hE, herr⟩ := radial_error P η B c₁ c₂ hc₁
  refine ⟨max (4 * G ^ 2) E, le_max_of_le_right hE, fun x z g g' hx hz hp => ?_⟩
  have hd := hp.decrease_pos
  obtain ⟨h1, h2⟩ := determinant_identity' P x z g g' hp.gradient_x
  have hdet : |determinant g (g' - g)| ≤ 4 * G ^ 2 :=
    determinant_gradient_bound hG.le ((hb x hx).2 g hp.gradient_x) ((hb z hz).2 g' hp.gradient_z)
  have he := herr x z g g' hx hz hp
  set ε := dot (g' - g) (radialDirection x) + 2 * pairCurvature x z g g'
  have heq : (2 * P.objective x - 2 * pairDecrease x z g) * pairCurvature x z g g' =
      -determinant g (g' - g) * stepDeterminant x z - pairDecrease x z g * ε := by
    have := h1.trans h2
    simp only [ε]
    nlinarith [this]
  rw [heq]
  have t1 : -determinant g (g' - g) * stepDeterminant x z ≤
      max (4 * G ^ 2) E * |stepDeterminant x z| := by
    calc -determinant g (g' - g) * stepDeterminant x z
        ≤ |determinant g (g' - g)| * |stepDeterminant x z| := by
          rw [← abs_mul]; exact neg_le_abs _ |>.trans_eq' (by ring)
      _ ≤ max (4 * G ^ 2) E * |stepDeterminant x z| :=
          mul_le_mul_of_nonneg_right (hdet.trans (le_max_left _ _)) (abs_nonneg _)
  have t2 : -(pairDecrease x z g * ε) ≤
      max (4 * G ^ 2) E * pairDecrease x z g * (|horizontalStep x z| + pairDecrease x z g) := by
    calc -(pairDecrease x z g * ε) = pairDecrease x z g * (-ε) := by ring
      _ ≤ pairDecrease x z g * |ε| := mul_le_mul_of_nonneg_left (neg_le_abs ε) hd.le
      _ ≤ pairDecrease x z g * (E * (|horizontalStep x z| + pairDecrease x z g)) :=
          mul_le_mul_of_nonneg_left he hd.le
      _ ≤ max (4 * G ^ 2) E * pairDecrease x z g * (|horizontalStep x z| + pairDecrease x z g) := by
          have := le_max_right (4 * G ^ 2) E
          have hs : 0 ≤ |horizontalStep x z| + pairDecrease x z g := by positivity
          nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hd.le hs)]
  linarith

/-- Item `C/10_Q/disp/020`, equation (10.14) (`companion/chapters/10_Q.tex:150-152`): "The exact
identity
\[ b_iD=2F(x)h+ud." \]
For an active branch $i$ at $x$ with gradient $g$ there, for every $z$ (library
`slope_determinant_identity`). -/
theorem slope_determinant {m : ℕ} (P : Parabolic.Family m) (x z g : Vec 2) (i : Fin m)
    (hi : P.Active i x) (hg : HasFDerivAt P.objective (gradientFunctional g) x) :
    P.b i * stepDeterminant x z =
      2 * P.objective x * horizontalStep x z + x 0 * pairDecrease x z g := by
  have hgi := P.active_eq_gradient hi hg
  subst hgi
  exact P.slope_determinant_identity hi

/-! ### The rescaling cancels first-order transport (`10_Q.tex:159-217`) -/

/-- Item `C/10_Q/disp/021` (`companion/chapters/10_Q.tex:161-163`): "Since $D\ne0$, define
\[ \lambda=1+\frac{h\ell}{D}. \]
Then $r(z)-\lambda r(x)$ is parallel to $s$." $\lambda$ is a variable with its defining equation
(the library's `quotientMultiplier x z`). -/
theorem quotient_multiplier (x z : Vec 2) (hD : stepDeterminant x z ≠ 0) (lam : ℝ)
    (hlam : lam = 1 + horizontalStep x z * normalStep x z / stepDeterminant x z) :
    lam = quotientMultiplier x z ∧
      ∃ μ : ℝ, radialDirection z - lam • radialDirection x = μ • pairStep x z := by
  refine ⟨hlam, stepMultiplier x z, ?_⟩
  rw [radial_direction_transport hD, hlam]
  simp only [quotientMultiplier]
  abel

/-- Item `C/10_Q/disp/022`, equation (10.15) (`companion/chapters/10_Q.tex:165-168`): "A direct
identity using $d=-2a_iuh-b_i\ell$ is
\[ \lambda-1+\frac{a_iu}{F(x)}h=-\frac{vhd}{F(x)D}." \]
For an active branch $i$ at $x$ with gradient $g$ there, $F(x)\ne0$, $D\ne0$. -/
theorem cancellation {m : ℕ} (P : Parabolic.Family m) (x z g : Vec 2) (i : Fin m)
    (hi : P.Active i x) (hg : HasFDerivAt P.objective (gradientFunctional g) x)
    (hF : P.objective x ≠ 0) (hD : stepDeterminant x z ≠ 0) :
    pairDecrease x z g = -2 * P.a i * x 0 * horizontalStep x z - P.b i * normalStep x z ∧
      quotientMultiplier x z - 1 + P.a i * x 0 / P.objective x * horizontalStep x z =
        -(x 1 * horizontalStep x z * pairDecrease x z g) /
          (P.objective x * stepDeterminant x z) := by
  have hgi := P.active_eq_gradient hi hg
  subst hgi
  refine ⟨?_, ?_⟩
  · simp [pairDecrease, pairStep, Parabolic.Family.branchGradient, horizontalStep, normalStep, dot,
      Fin.sum_univ_two]
    ring
  · have h := P.quotient_cancellation hi hF hD
    rw [h]
    ring

/-- Band constants: $|u|,|v|\le R$ on the band. -/
theorem band_radius {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Vec 2, η ≤ P.objective x ∧ P.objective x ≤ B → ∀ k, |x k| ≤ R := by
  obtain ⟨R, hR, hrad⟩ := compact_sqNorm_radius (band_compact P η B) (0 : Vec 2)
  exact ⟨R, hR, fun x hx k =>
    abs_coordinate_of_sqNorm_le hR.le (by simpa only [sub_zero] using hrad x hx) k⟩

/-- Item `C/10_Q/disp/023` (`companion/chapters/10_Q.tex:170-173`), with the claims of line 169:
"By (10.13), the right side is $O(d)$ uniformly on the band. Since $h^2=O(d)$,
\[ \lambda=1+O(\sqrt d)>0,\qquad \log\lambda=-\frac{a_iu}{F(x)}h+O(d)." \]
On the band $\{\eta\le F\le B\}$ ($\eta>0$, $0\le c_1$, $c_2<1$): constants $C$ and $\delta>0$
chosen before the pairs such that every eligible pair in the band with $d\le\delta$ and every active
$i$ at $x$ satisfy $D\ne0$, $|vhd/(F(x)D)|\le Cd$, $h^2\le Cd$, $|\lambda-1|\le C\sqrt d$,
$\lambda>0$ and $|\log\lambda+(a_iu/F(x))h|\le Cd$. -/
theorem multiplier_estimates {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (hη : 0 < η)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x z g g' : Vec 2, ∀ i : Fin m,
      η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
      EligiblePair P.objective c₁ c₂ x z g g' → P.Active i x → pairDecrease x z g ≤ δ →
      stepDeterminant x z ≠ 0 ∧
      |x 1 * horizontalStep x z * pairDecrease x z g / (P.objective x * stepDeterminant x z)| ≤
        C * pairDecrease x z g ∧
      (horizontalStep x z) ^ 2 ≤ C * pairDecrease x z g ∧
      |quotientMultiplier x z - 1| ≤ C * Real.sqrt (pairDecrease x z g) ∧
      0 < quotientMultiplier x z ∧
      |Real.log (quotientMultiplier x z) + P.a i * x 0 / P.objective x * horizontalStep x z| ≤
        C * pairDecrease x z g := by
  obtain ⟨CD, δD, hCD, hδD, hden⟩ := denominator_bounds P η B hη c₁ c₂ hc₁ hc₂
  obtain ⟨R, hR, hrad⟩ := band_radius P η B
  have hA := P.maxQuadratic_pos
  have ha := P.minQuadratic_pos
  set Bc := R * CD / η
  set T := P.maxQuadratic * R / η
  set S := 2 * T ^ 2 / P.minQuadratic + 2 * Bc ^ 2
  have hBc : 0 ≤ Bc := by positivity
  have hT : 0 ≤ T := by positivity
  have hS : 0 ≤ S := by positivity
  set C := Bc + 1 / P.minQuadratic + Real.sqrt S + (2 * S + Bc) with hCdef
  have h1a : 0 ≤ 1 / P.minQuadratic := by positivity
  have h1s : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  have hC : 0 ≤ C := by positivity
  have hCB : Bc ≤ C := by rw [hCdef]; linarith
  have hCa : 1 / P.minQuadratic ≤ C := by rw [hCdef]; linarith
  have hCs : Real.sqrt S ≤ C := by rw [hCdef]; linarith
  have hCl : 2 * S + Bc ≤ C := by rw [hCdef]; linarith
  set δ := min δD (min 1 (1 / (4 * (S + 1))))
  have hδ : 0 < δ := lt_min hδD (lt_min one_pos (by positivity))
  refine ⟨C, δ, hC, hδ, fun x z g g' i hx hz hp hi hdδ => ?_⟩
  have hd := hp.decrease_pos
  have hd1 : pairDecrease x z g ≤ 1 := hdδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdsmall : pairDecrease x z g ≤ 1 / (4 * (S + 1)) :=
    hdδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, hhD, hD⟩ := hden x z g g' hx hz hp (hdδ.trans (min_le_left _ _))
  have hxp : 0 < P.objective x := hη.trans_le hx.1
  set α := P.a i * x 0 / P.objective x
  have hα : |α| ≤ T := by
    simp only [α, T]
    rw [abs_div, abs_mul, abs_of_pos (P.a_pos i), abs_of_pos hxp]
    exact ratio_bound (mul_nonneg (P.a_pos i).le (abs_nonneg _))
      (mul_le_mul (P.le_maxQuadratic i) (hrad x hx 0) (abs_nonneg _) hA.le) hη hx.1
  obtain ⟨-, hcanc⟩ := cancellation P x z g i hi hp.gradient_x hxp.ne' hD
  have hres : |quotientMultiplier x z - 1 + α * horizontalStep x z| ≤ Bc * pairDecrease x z g :=
    cancellation_residual_bound hη hx.1 hD hR.le hCD.le hd.le (hrad x hx 1) hhD
      (by rw [hcanc]; ring)
  have hhor := P.eligible_horizontal_sq_le hc₁ hi hp
  have hsq : (quotientMultiplier x z - 1) ^ 2 ≤ S * pairDecrease x z g :=
    compensation_square_bound ha hT hBc hd.le hd1 hα hhor hres
  obtain ⟨hclose, hbase⟩ := close_multiplier_of_small_decrease hS hd.le hdsmall hsq
  have hlog := compensation_log_bound hd.le hclose hsq hres
  have hdpos := hd.le
  refine ⟨hD, ?_, ?_, ?_, hbase, ?_⟩
  · have h1 : |x 1 * horizontalStep x z * pairDecrease x z g /
          (P.objective x * stepDeterminant x z)|
        = |quotientMultiplier x z - 1 + α * horizontalStep x z| := by
      rw [hcanc, neg_div, abs_neg]
    rw [h1]
    exact hres.trans (mul_le_mul_of_nonneg_right hCB hdpos)
  · rw [le_div_iff₀ ha] at hhor
    have : (horizontalStep x z) ^ 2 ≤ 1 / P.minQuadratic * pairDecrease x z g := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]; linarith
    exact this.trans (mul_le_mul_of_nonneg_right hCa hdpos)
  · have hs : |quotientMultiplier x z - 1| ≤ Real.sqrt S * Real.sqrt (pairDecrease x z g) := by
      rw [← Real.sqrt_mul hS, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    exact hs.trans (mul_le_mul_of_nonneg_right hCs (Real.sqrt_nonneg _))
  · exact hlog.trans (mul_le_mul_of_nonneg_right hCl hdpos)

/-- Item `C/10_Q/disp/024` (`companion/chapters/10_Q.tex:175-178`), with the claim of line 174 and
the conclusion of line 179: "For the old branch's exponent $L_i(x)=a_iu^2/(2F(x))+k_i$,
smoothness in the two scalar arguments $(u,F)$ on the positive band gives
\[ L_i(z)-L_i(x)=\frac{a_iu}{F(x)}h+O(h^2+\Delta)=\frac{a_iu}{F(x)}h+O(d). \]
Thus $\log\lambda+L_i(z)-L_i(x)=O(d)$." With $L_i$ (a variable with its defining equation), the
remainder is exactly $a_ih^2/(2F(x))+a_iu'^2\Delta/(2F(x)F(z))$; on the band, constants $C$,
$\delta$ chosen before the pairs bound it by $C(h^2+\Delta)$ and by $Cd$, and
$|\log\lambda+L_i(z)-L_i(x)|\le Cd$, for eligible pairs in the band with $d\le\delta$. -/
theorem exponent_estimates {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (hη : 0 < η)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) (L : Fin m → Vec 2 → ℝ)
    (hL : ∀ i y, L i y = P.a i * (y 0) ^ 2 / (2 * P.objective y) + P.calibration i) :
    (∀ (x z : Vec 2) (i : Fin m), P.objective x ≠ 0 → P.objective z ≠ 0 →
      L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z =
        P.a i * (horizontalStep x z) ^ 2 / (2 * P.objective x) +
          P.a i * (z 0) ^ 2 * (P.objective x - P.objective z) /
            (2 * P.objective x * P.objective z)) ∧
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x z g g' : Vec 2, ∀ i : Fin m,
      η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
      EligiblePair P.objective c₁ c₂ x z g g' → P.Active i x → pairDecrease x z g ≤ δ →
      |L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z| ≤
        C * ((horizontalStep x z) ^ 2 + (P.objective x - P.objective z)) ∧
      |L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z| ≤ C * pairDecrease x z g ∧
      |Real.log (quotientMultiplier x z) + L i z - L i x| ≤ C * pairDecrease x z g := by
  have hid : ∀ (x z : Vec 2) (i : Fin m), P.objective x ≠ 0 → P.objective z ≠ 0 →
      L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z =
        P.a i * (horizontalStep x z) ^ 2 / (2 * P.objective x) +
          P.a i * (z 0) ^ 2 * (P.objective x - P.objective z) /
            (2 * P.objective x * P.objective z) := by
    intro x z i hx hz
    rw [hL, hL]
    have h := P.exponent_increment (i := i) hx hz
    linear_combination h
  refine ⟨hid, ?_⟩
  obtain ⟨C1, δ1, hC1, hδ1, hm⟩ := multiplier_estimates P η B hη c₁ c₂ hc₁ hc₂
  obtain ⟨R, hR, hrad⟩ := band_radius P η B
  have hA := P.maxQuadratic_pos
  have ha := P.minQuadratic_pos
  set U := P.maxQuadratic / (2 * η * P.minQuadratic) + P.maxQuadratic * R ^ 2 / (2 * η ^ 2)
  set V := P.maxQuadratic / (2 * η) + P.maxQuadratic * R ^ 2 / (2 * η ^ 2)
  have hU : 0 ≤ U := by positivity
  have hV : 0 ≤ V := by positivity
  refine ⟨U + V + C1, δ1, by positivity, hδ1, fun x z g g' i hx hz hp hi hdδ => ?_⟩
  have hd := hp.decrease_pos
  have hxp : 0 < P.objective x := hη.trans_le hx.1
  have hzp : 0 < P.objective z := hη.trans_le hz.1
  have hdrop : 0 ≤ P.objective x - P.objective z := (mul_nonneg hc₁ hd.le).trans hp.armijo
  have hhor := P.eligible_horizontal_sq_le hc₁ hi hp
  have hzsq : (z 0) ^ 2 ≤ R ^ 2 := by
    have := hrad z hz 0
    nlinarith [sq_abs (z 0), abs_nonneg (z 0)]
  have hrem := hid x z i hxp.ne' hzp.ne'
  -- the bound by h² + Δ
  have hb1 : |L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z| ≤
      V * ((horizontalStep x z) ^ 2 + (P.objective x - P.objective z)) := by
    rw [hrem, abs_of_nonneg (by have := (P.a_pos i).le; positivity)]
    have t1 : P.a i * (horizontalStep x z) ^ 2 / (2 * P.objective x) ≤
        P.maxQuadratic / (2 * η) * (horizontalStep x z) ^ 2 := by
      rw [div_mul_eq_mul_div]
      exact ratio_bound (mul_nonneg (P.a_pos i).le (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (P.le_maxQuadratic i) (sq_nonneg _)) (by positivity)
        (by linarith [hx.1])
    have t2 : P.a i * (z 0) ^ 2 * (P.objective x - P.objective z) /
        (2 * P.objective x * P.objective z) ≤
        P.maxQuadratic * R ^ 2 / (2 * η ^ 2) * (P.objective x - P.objective z) := by
      rw [div_mul_eq_mul_div]
      exact ratio_bound (by have := (P.a_pos i).le; positivity)
        (mul_le_mul_of_nonneg_right (mul_le_mul (P.le_maxQuadratic i) hzsq (sq_nonneg _) hA.le)
          hdrop) (by positivity) (by nlinarith [mul_le_mul hx.1 hz.1 hη.le hxp.le])
    have : V * ((horizontalStep x z) ^ 2 + (P.objective x - P.objective z)) =
        (P.maxQuadratic / (2 * η) + P.maxQuadratic * R ^ 2 / (2 * η ^ 2)) *
          ((horizontalStep x z) ^ 2 + (P.objective x - P.objective z)) := rfl
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ P.maxQuadratic * R ^ 2 / (2 * η ^ 2))
      (sq_nonneg (horizontalStep x z)),
      mul_nonneg (by positivity : (0 : ℝ) ≤ P.maxQuadratic / (2 * η)) hdrop]
  -- the bound by d
  have hb2 : |L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z| ≤
      U * pairDecrease x z g := by
    rw [hrem]
    exact exponent_remainder_bound (P.a_pos i).le (P.le_maxQuadratic i) hη hx.1 hz.1 ha hd.le
      hdrop hp.convex_decrease hhor hzsq
  obtain ⟨-, -, -, -, -, hlog⟩ := hm x z g g' i hx hz hp hi hdδ
  have hdpos := hd.le
  have hhd : 0 ≤ (horizontalStep x z) ^ 2 + (P.objective x - P.objective z) := by positivity
  refine ⟨hb1.trans (mul_le_mul_of_nonneg_right (by linarith) hhd),
    hb2.trans (mul_le_mul_of_nonneg_right (by linarith) hdpos), ?_⟩
  have hsum := (abs_add (Real.log (quotientMultiplier x z) + P.a i * x 0 / P.objective x *
    horizontalStep x z) (L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z)).trans
    (add_le_add hlog hb2)
  have he : Real.log (quotientMultiplier x z) + P.a i * x 0 / P.objective x * horizontalStep x z +
      (L i z - L i x - P.a i * x 0 / P.objective x * horizontalStep x z) =
      Real.log (quotientMultiplier x z) + L i z - L i x := by ring
  rw [he] at hsum
  calc |Real.log (quotientMultiplier x z) + L i z - L i x| ≤ C1 * pairDecrease x z g +
        U * pairDecrease x z g := hsum
    _ ≤ (U + V + C1) * pairDecrease x z g := by nlinarith

/-- Item `C/10_Q/disp/025`, equation (10.16) (`companion/chapters/10_Q.tex:182-184`), with the
claim of line 181: "We still need to account for a change from branch $i$ to branch $j$. The
finite-envelope geometry implies
\[ |L_j(z)-L_i(z)|\le C\frac{e}{F(z)}\le C_\eta d." \]
A constant $C$ chosen from the family alone gives the first inequality at every $z$ with $F(z)>0$,
every branch $i$ and every active $j$ at $z$ ($e=F(z)-(a_iu'^2+b_iv')$; library
`exists_calibration_deficit_bound`); on the band ($0\le c_1$) the second follows with
$C_\eta=C/\eta$ for eligible pairs with $i$ active at $x$. -/
theorem branch_change {m : ℕ} (P : Parabolic.Family m) (L : Fin m → Vec 2 → ℝ)
    (hL : ∀ i y, L i y = P.a i * (y 0) ^ 2 / (2 * P.objective y) + P.calibration i) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (i j : Fin m) (z : Vec 2), P.Active j z → 0 < P.objective z →
        |L j z - L i z| ≤ C * (P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1)) / P.objective z) ∧
      ∀ (η B c₁ c₂ : ℝ), 0 < η → 0 ≤ c₁ → ∀ (x z g g' : Vec 2) (i j : Fin m),
        η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
        EligiblePair P.objective c₁ c₂ x z g g' → P.Active i x → P.Active j z →
        C * (P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1)) / P.objective z ≤
          C / η * pairDecrease x z g := by
  obtain ⟨C, hC, hb⟩ := P.exists_calibration_deficit_bound
  have hLd : ∀ (i j : Fin m) (z : Vec 2), L j z - L i z =
      (P.a j - P.a i) * (z 0) ^ 2 / (2 * P.objective z) + P.calibration j - P.calibration i := by
    intro i j z; rw [hL, hL]; ring
  refine ⟨C, hC, fun i j z hj hz => ?_, fun η B c₁ c₂ hη hc₁ x z g g' i j hx hz hp hi hj => ?_⟩
  · rw [hLd]; exact hb i j z hj hz
  · have he : P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1) ≤ pairDecrease x z g :=
      P.eligible_deficit_le hc₁ hi hp
    have he0 : 0 ≤ P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1) := P.deficit_nonneg i z
    rw [div_mul_eq_mul_div]
    exact ratio_bound (mul_nonneg hC.le he0) (mul_le_mul_of_nonneg_left he hC.le) hη hz.1

/-- Item `C/10_Q/disp/027` (`companion/chapters/10_Q.tex:190-192`), with its normalization display
`C/10_Q/disp/026` (lines 186-188) and the claims of lines 189 and 193: "Normalize a point by
$t_0=u'^2/F(z)$, $v_0=v'/F(z)$. It lies on the compact polygonal arc
\[ S=\{(t_0,v_0):t_0\ge0,\ \max_i(a_it_0+b_iv_0)=1\}. \]
Compactness follows from $t_0\le1/a_{\min}$ and the two nonzero extreme normal slopes." With $S$
a variable with its defining equation (the maximum written with `Finset.sup'`): for $F(z)>0$ the
normalized point lies in $S$; every point of $S$ has $t_0\le1/a_{\min}$ and $v_0$ between the
reciprocals of a negative and a positive slope (`normalLeft`, `normalRight`); $S$ is compact. -/
theorem normalized_arc {m : ℕ} (P : Parabolic.Family m) (S : Set (ℝ × ℝ))
    (hS : S = {p | 0 ≤ p.1 ∧
      Finset.univ.sup' P.indices_nonempty (fun i => P.a i * p.1 + P.b i * p.2) = 1}) :
    (∀ z : Vec 2, 0 < P.objective z → ((z 0) ^ 2 / P.objective z, z 1 / P.objective z) ∈ S) ∧
      (∀ p ∈ S, p.1 ≤ 1 / P.minQuadratic ∧ p.2 ∈ Icc P.normalLeft P.normalRight) ∧
      IsCompact S := by
  have hle : ∀ p ∈ S, ∀ i, P.a i * p.1 + P.b i * p.2 ≤ 1 := by
    intro p hp i
    rw [hS] at hp
    rw [← hp.2]
    exact Finset.le_sup' (fun i => P.a i * p.1 + P.b i * p.2) (Finset.mem_univ i)
  have hbounds : ∀ p ∈ S, p.1 ≤ 1 / P.minQuadratic ∧ p.2 ∈ Icc P.normalLeft P.normalRight := by
    intro p hp
    have hp0 : 0 ≤ p.1 := by rw [hS] at hp; exact hp.1
    refine ⟨?_, P.normalized_normal_bounds hp0 (hle p hp)⟩
    obtain ⟨i, hi⟩ := P.negative_slope
    obtain ⟨j, hj⟩ := P.positive_slope
    have h1 := hle p hp i
    have h2 := hle p hp j
    rw [le_div_iff₀ P.minQuadratic_pos]
    -- the convex combination with slope zero
    have hlam : 0 < P.b j - P.b i := by linarith
    have hcomb : (P.b j * P.a i - P.b i * P.a j) * p.1 ≤ P.b j - P.b i := by nlinarith
    have hmi := P.minQuadratic_le i
    have hmj := P.minQuadratic_le j
    have : P.minQuadratic * (P.b j - P.b i) ≤ P.b j * P.a i - P.b i * P.a j := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hp0]
  refine ⟨fun z hz => ?_, hbounds, ?_⟩
  · rw [hS]
    refine ⟨div_nonneg (sq_nonneg _) hz.le, ?_⟩
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      have := P.branch_le i z
      simp only [Parabolic.Family.branch] at this
      rw [mul_div_assoc', mul_div_assoc', div_add_div_same, div_le_one hz]
      linarith
    · obtain ⟨i, hi⟩ := P.exists_active z
      refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun i => P.a i * ((z 0) ^ 2 / P.objective z) +
        P.b i * (z 1 / P.objective z)) (Finset.mem_univ i))
      show 1 = P.a i * ((z 0) ^ 2 / P.objective z) + P.b i * (z 1 / P.objective z)
      rw [mul_div_assoc', mul_div_assoc', div_add_div_same, eq_div_iff hz.ne', one_mul]
      exact hi
  · apply Metric.isCompact_of_isClosed_isBounded
    · rw [hS]
      apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
      apply isClosed_eq _ continuous_const
      apply Continuous.finset_sup'_apply
      intro i _
      fun_prop
    · apply (Metric.isBounded_Icc ((0 : ℝ), P.normalLeft)
        (1 / P.minQuadratic, P.normalRight)).subset
      intro p hp
      have hp0 : 0 ≤ p.1 := by rw [hS] at hp; exact hp.1
      obtain ⟨h1, h2⟩ := hbounds p hp
      exact ⟨⟨hp0, h2.1⟩, ⟨h1, h2.2⟩⟩

/-- The range of the coordinate $v_0$ on the normalized arc: $v\in[1/\min_ib_i,1/\max_ib_i]$
exactly when $b_iv\le1$ for every branch $i$. -/
theorem arc_range_iff {m : ℕ} (P : Parabolic.Family m) (v : ℝ) :
    v ∈ Icc (Finset.univ.inf' P.indices_nonempty P.b)⁻¹
        (Finset.univ.sup' P.indices_nonempty P.b)⁻¹ ↔ ∀ i, P.b i * v ≤ 1 := by
  set bmin := Finset.univ.inf' P.indices_nonempty P.b with hbmin
  set bmax := Finset.univ.sup' P.indices_nonempty P.b with hbmax
  have hbmin_neg : bmin < 0 := by
    obtain ⟨i, hi⟩ := P.negative_slope
    exact lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ i)) hi
  have hbmax_pos : 0 < bmax := by
    obtain ⟨i, hi⟩ := P.positive_slope
    exact lt_of_lt_of_le hi (Finset.le_sup' _ (Finset.mem_univ i))
  constructor
  · rintro ⟨h1, h2⟩ i
    rcases le_or_lt 0 v with hv | hv
    · have hb : P.b i ≤ bmax := Finset.le_sup' P.b (Finset.mem_univ i)
      have hm : bmax * v ≤ 1 := by
        calc bmax * v ≤ bmax * bmax⁻¹ := mul_le_mul_of_nonneg_left h2 hbmax_pos.le
          _ = 1 := mul_inv_cancel₀ hbmax_pos.ne'
      nlinarith [mul_le_mul_of_nonneg_right hb hv]
    · have hb : bmin ≤ P.b i := Finset.inf'_le P.b (Finset.mem_univ i)
      have hm : bmin * v ≤ 1 := by
        calc bmin * v ≤ bmin * bmin⁻¹ := mul_le_mul_of_nonpos_left h1 hbmin_neg.le
          _ = 1 := mul_inv_cancel₀ hbmin_neg.ne
      nlinarith [mul_le_mul_of_nonpos_right hb hv.le]
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' P.indices_nonempty P.b
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' P.indices_nonempty P.b
    have hi' : bmin = P.b i := hi
    have hj' : bmax = P.b j := hj
    refine ⟨?_, ?_⟩
    · have h' : bmin * v ≤ 1 := by rw [hi']; exact h i
      rw [inv_eq_one_div, div_le_iff_of_neg hbmin_neg]
      linarith
    · have h' : bmax * v ≤ 1 := by rw [hj']; exact h j
      rw [inv_eq_one_div, le_div_iff₀ hbmax_pos]
      linarith

/-- Item `C/10_Q/prose/022` (`companion/chapters/10_Q.tex:189`): "It lies on the compact polygonal
arc" $S$ of display `disp/027` (membership and compactness: `normalized_arc`). With
$\tau(v_0)=\min_i(1-b_iv_0)/a_i$ (a variable with this defining equation, the minimum written with
`Finset.inf'`), a minimum of finitely many affine functions: $S$ is the graph $t_0=\tau(v_0)$ over
the compact interval $[1/\min_ib_i,1/\max_ib_i]$, $\tau$ is continuous, and $S$ is the union of the
finitely many convex pieces $S\cap\{a_it_0+b_iv_0=1\}$ (its segments). -/
theorem arc_graph {m : ℕ} (P : Parabolic.Family m) (S : Set (ℝ × ℝ))
    (hS : S = {p | 0 ≤ p.1 ∧
      Finset.univ.sup' P.indices_nonempty (fun i => P.a i * p.1 + P.b i * p.2) = 1})
    (τ : ℝ → ℝ)
    (hτ : ∀ v, τ v = Finset.univ.inf' P.indices_nonempty (fun i => (1 - P.b i * v) / P.a i)) :
    S = {p | p.2 ∈ Icc (Finset.univ.inf' P.indices_nonempty P.b)⁻¹
        (Finset.univ.sup' P.indices_nonempty P.b)⁻¹ ∧ p.1 = τ p.2} ∧
      Continuous τ ∧
      S = ⋃ i, {p | p ∈ S ∧ P.a i * p.1 + P.b i * p.2 = 1} ∧
      ∀ i, Convex ℝ {p : ℝ × ℝ | p ∈ S ∧ P.a i * p.1 + P.b i * p.2 = 1} := by
  set bmin := Finset.univ.inf' P.indices_nonempty P.b with hbmin
  set bmax := Finset.univ.sup' P.indices_nonempty P.b with hbmax
  have hbmin_neg : bmin < 0 := by
    obtain ⟨i, hi⟩ := P.negative_slope
    exact lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ i)) hi
  have hbmax_pos : 0 < bmax := by
    obtain ⟨i, hi⟩ := P.positive_slope
    exact lt_of_lt_of_le hi (Finset.le_sup' _ (Finset.mem_univ i))
  have hmemS : ∀ p : ℝ × ℝ, p ∈ S ↔ 0 ≤ p.1 ∧ (∀ i, P.a i * p.1 + P.b i * p.2 ≤ 1) ∧
      ∃ i, P.a i * p.1 + P.b i * p.2 = 1 := by
    intro p
    rw [hS]
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨h0, fun i => ?_, ?_⟩
      · rw [← h1]
        exact Finset.le_sup' (fun i => P.a i * p.1 + P.b i * p.2) (Finset.mem_univ i)
      · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' P.indices_nonempty
          (fun i => P.a i * p.1 + P.b i * p.2)
        exact ⟨i, by rw [← hi]; exact h1⟩
    · rintro ⟨h0, hle, i, hi⟩
      refine ⟨h0, le_antisymm (Finset.sup'_le _ _ fun j _ => hle j) ?_⟩
      rw [← hi]
      exact Finset.le_sup' (fun i => P.a i * p.1 + P.b i * p.2) (Finset.mem_univ i)
  have hdom : ∀ v : ℝ, v ∈ Icc bmin⁻¹ bmax⁻¹ ↔ ∀ i, P.b i * v ≤ 1 := arc_range_iff P
  have hgraph : S = {p | p.2 ∈ Icc bmin⁻¹ bmax⁻¹ ∧ p.1 = τ p.2} := by
    ext p
    rw [hmemS p]
    simp only [mem_setOf_eq]
    rw [hdom p.2, hτ]
    constructor
    · rintro ⟨h0, hle, i, hi⟩
      refine ⟨fun j => ?_, le_antisymm ?_ ?_⟩
      · have := hle j
        nlinarith [mul_nonneg (P.a_pos j).le h0]
      · exact Finset.le_inf' _ _ fun j _ => by
          rw [le_div_iff₀ (P.a_pos j)]
          have := hle j
          linarith
      · refine (Finset.inf'_le _ (Finset.mem_univ i)).trans (le_of_eq ?_)
        rw [div_eq_iff (P.a_pos i).ne']
        linarith
    · rintro ⟨hb, hp⟩
      have hle : ∀ j, p.1 ≤ (1 - P.b j * p.2) / P.a j := fun j => by
        rw [hp]
        exact Finset.inf'_le _ (Finset.mem_univ j)
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' P.indices_nonempty
        (fun i => (1 - P.b i * p.2) / P.a i)
      refine ⟨?_, fun j => ?_, i, ?_⟩
      · rw [hp]
        exact Finset.le_inf' _ _ fun j _ => div_nonneg (by linarith [hb j]) (P.a_pos j).le
      · have := hle j
        rw [le_div_iff₀ (P.a_pos j)] at this
        linarith
      · rw [hp, hi]
        have := (P.a_pos i).ne'
        field_simp
  have hunion : S = ⋃ i, {p | p ∈ S ∧ P.a i * p.1 + P.b i * p.2 = 1} := by
    ext p
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · intro hp
      obtain ⟨_, _, i, hi⟩ := (hmemS p).mp hp
      exact ⟨i, hp, hi⟩
    · rintro ⟨i, hp, _⟩
      exact hp
  have hconv : ∀ i, Convex ℝ {p : ℝ × ℝ | p ∈ S ∧ P.a i * p.1 + P.b i * p.2 = 1} := by
    intro i p hp q hq α β hα hβ hαβ
    obtain ⟨hp0, hple, -⟩ := (hmemS p).mp hp.1
    obtain ⟨hq0, hqle, -⟩ := (hmemS q).mp hq.1
    have hi : P.a i * (α • p + β • q).1 + P.b i * (α • p + β • q).2 = 1 := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination α * hp.2 + β * hq.2 + hαβ
    refine ⟨(hmemS _).mpr ⟨?_, fun j => ?_, i, hi⟩, hi⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      exact add_nonneg (mul_nonneg hα hp0) (mul_nonneg hβ hq0)
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      have h1 := hple j
      have h2 := hqle j
      nlinarith [mul_le_mul_of_nonneg_left h1 hα, mul_le_mul_of_nonneg_left h2 hβ]
  refine ⟨hgraph, ?_, hunion, hconv⟩
  rw [show τ = fun v => Finset.univ.inf' P.indices_nonempty (fun i => (1 - P.b i * v) / P.a i)
    from funext hτ]
  apply Continuous.finset_inf'_apply
  intro i _
  fun_prop

/-- Item `C/10_Q/disp/028` (`companion/chapters/10_Q.tex:194-197`): "On the segment where $j$ is
active, both
\[ e/F(z)=1-a_it_0-b_iv_0,\qquad L_j-L_i=(a_j-a_i)t_0/2+k_j-k_i \]
are affine functions." For $F(z)>0$ and $j$ active at $z$, with $t_0$, $v_0$ the normalized
coordinates: both identities, $t_0=(1-b_jv_0)/a_j$ on $j$'s segment (`normalizedQuadratic`), and
both functions are affine in $v_0$ there (library `envelopeDeficit_affine`,
`envelopeExponentDifference_affine`). -/
theorem segment_affine {m : ℕ} (P : Parabolic.Family m) (L : Fin m → Vec 2 → ℝ)
    (hL : ∀ i y, L i y = P.a i * (y 0) ^ 2 / (2 * P.objective y) + P.calibration i)
    (z : Vec 2) (hz : 0 < P.objective z) (i j : Fin m) (hj : P.Active j z)
    (t0 v0 : ℝ) (ht0 : t0 = (z 0) ^ 2 / P.objective z) (hv0 : v0 = z 1 / P.objective z) :
    (P.objective z - (P.a i * (z 0) ^ 2 + P.b i * z 1)) / P.objective z =
        1 - P.a i * t0 - P.b i * v0 ∧
      L j z - L i z = (P.a j - P.a i) * t0 / 2 + P.calibration j - P.calibration i ∧
      t0 = (1 - P.b j * v0) / P.a j ∧
      1 - P.a i * t0 - P.b i * v0 = (1 - P.a i / P.a j) + (P.a i * P.b j / P.a j - P.b i) * v0 ∧
      (P.a j - P.a i) * t0 / 2 + P.calibration j - P.calibration i =
        ((P.a j - P.a i) / 2 / P.a j + P.calibration j - P.calibration i) +
          (-(P.a j - P.a i) / 2 * (P.b j / P.a j)) * v0 := by
  have hcell := (P.active_normalized_cell hj hz).1
  have ht0' : t0 = (1 - P.b j * v0) / P.a j := by
    rw [ht0, hv0, ← hcell]; rfl
  have haj := (P.a_pos j).ne'
  refine ⟨?_, ?_, ht0', ?_, ?_⟩
  · rw [ht0, hv0]; field_simp; ring
  · rw [hL, hL, ht0]; ring
  · rw [ht0']; field_simp; ring
  · rw [ht0']; field_simp; ring

/-- Item `C/10_Q/prose/024` (`companion/chapters/10_Q.tex:198`): "The first is nonnegative.
Whenever it vanishes, the second vanishes by (10.7)." On each cell (segment) of the envelope,
parametrized by $v_0$ (`envelopeCell j`), for every branch $i$: the first function
(`envelopeDeficit i j`) is nonnegative and where it vanishes so does the second
(`envelopeExponentDifference i j`). Also (item `prose/026`, "There are finitely many segments and
pairs, proving (10.16)"): one constant $C$ for the finitely many pairs bounds the second by $C$
times the first on every segment (the case analysis of `segment_cases` is replaced in the library
proof of `cell_pair_deficit_bound` by one affine-function lemma); (10.16) itself is `branch_change`.
(The references printed "(12)", "(13)", "(7)" and "(16)" before the correction M28 of 15 October
2026.) And the
pruned family has the same objective and the same gradients at differentiable points. -/
theorem segment_bound_facts {m : ℕ} (P : Parabolic.Family m) :
    (∀ i j v, v ∈ P.envelopeCell j → 0 ≤ P.envelopeDeficit i j v) ∧
      (∀ i j v, v ∈ P.envelopeCell j → P.envelopeDeficit i j v = 0 →
        P.envelopeExponentDifference i j v = 0) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ i j v, v ∈ P.envelopeCell j →
        |P.envelopeExponentDifference i j v| ≤ C * P.envelopeDeficit i j v) ∧
      (∀ x, P.prunedFamily.objective x = P.objective x) ∧
      (∀ x g, HasFDerivAt P.objective (gradientFunctional g) x →
        HasFDerivAt P.prunedFamily.objective (gradientFunctional g) x) :=
  ⟨fun i _ _ hv => P.envelopeDeficit_nonneg i hv,
    fun _ _ _ hv hz => P.envelopeExponentDifference_zero_of_deficit_zero hv hz,
    P.exists_uniform_cell_deficit_bound, P.prunedFamily_objective,
    fun _ _ hg => P.prunedFamily_gradient hg⟩

/-- Item `C/10_Q/prose/025` (`companion/chapters/10_Q.tex:198`): "On an adjacent segment the two
functions are proportional; on a nonadjacent segment the first has a positive minimum." With $S$
the arc of display `disp/027` and the segment of branch $k$ in the coordinate $v_0$,
$S_k=\{v_0:\exists t_0,\ (t_0,v_0)\in S,\ a_kt_0+b_kv_0=1\}$ (variables with their defining
equations): $S_k$ is the library's cell `envelopeCell k` cut to the arc's range
$[1/\min_ib_i,1/\max_ib_i]$; the first function vanishes somewhere on $S_j$ exactly when the
segments $S_i$ and $S_j$ meet (adjacent segments); then the two functions are proportional (on the
whole line); when they do not meet (nonadjacent) and $S_j$ is nonempty, the first function has a
positive minimum on $S_j$. -/
theorem segment_cases {m : ℕ} (P : Parabolic.Family m) (S : Set (ℝ × ℝ))
    (hS : S = {p | 0 ≤ p.1 ∧
      Finset.univ.sup' P.indices_nonempty (fun i => P.a i * p.1 + P.b i * p.2) = 1})
    (seg : Fin m → Set ℝ)
    (hseg : ∀ k, seg k = {v | ∃ t, (t, v) ∈ S ∧ P.a k * t + P.b k * v = 1}) (i j : Fin m) :
    (∀ k, seg k = P.envelopeCell k ∩ Icc (Finset.univ.inf' P.indices_nonempty P.b)⁻¹
        (Finset.univ.sup' P.indices_nonempty P.b)⁻¹) ∧
      ((∃ v ∈ seg j, P.envelopeDeficit i j v = 0) ↔ (seg i ∩ seg j).Nonempty) ∧
      ((seg i ∩ seg j).Nonempty →
        ∃ c : ℝ, ∀ v, P.envelopeExponentDifference i j v = c * P.envelopeDeficit i j v) ∧
      ((seg j).Nonempty → seg i ∩ seg j = ∅ →
        ∃ μ : ℝ, 0 < μ ∧ ∀ v ∈ seg j, μ ≤ P.envelopeDeficit i j v) := by
  set I := Icc (Finset.univ.inf' P.indices_nonempty P.b)⁻¹
    (Finset.univ.sup' P.indices_nonempty P.b)⁻¹ with hI
  -- the segments are the cells cut to the arc's range
  have hcell : ∀ k, seg k = P.envelopeCell k ∩ I := by
    intro k
    ext v
    rw [hseg k, hS]
    simp only [mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨t, ⟨ht0, hsup⟩, hk⟩
      have hle : ∀ l, P.a l * t + P.b l * v ≤ 1 := fun l => by
        rw [← hsup]
        exact Finset.le_sup' (fun i => P.a i * t + P.b i * v) (Finset.mem_univ l)
      refine ⟨(P.normalized_cell_of_active ht0 hle hk).2, (arc_range_iff P v).mpr fun l => ?_⟩
      have := hle l
      nlinarith [mul_nonneg (P.a_pos l).le ht0]
    · rintro ⟨hv, hrange⟩
      have hb := (arc_range_iff P v).mp hrange
      have hid : ∀ l, P.a l * P.normalizedQuadratic l v + P.b l * v = 1 :=
        fun l => P.normalizedQuadratic_identity l v
      refine ⟨P.normalizedQuadratic k v, ⟨?_, le_antisymm ?_ ?_⟩, hid k⟩
      · unfold Parabolic.Family.normalizedQuadratic
        exact div_nonneg (by linarith [hb k]) (P.a_pos k).le
      · refine Finset.sup'_le _ _ fun l _ => ?_
        have h1 := mul_le_mul_of_nonneg_left (hv.2 l) (P.a_pos l).le
        linarith [hid l]
      · rw [← hid k]
        exact Finset.le_sup' (fun i => P.a i * P.normalizedQuadratic k v + P.b i * v)
          (Finset.mem_univ k)
  -- on a cell, the first function vanishes exactly at the points of the other cell
  have hzero : ∀ v ∈ P.envelopeCell j, P.envelopeDeficit i j v = 0 ↔ v ∈ P.envelopeCell i := by
    intro v hv
    have hid := P.normalizedQuadratic_identity i v
    have hai := P.a_pos i
    constructor
    · intro hz
      have he : P.normalizedQuadratic i v = P.normalizedQuadratic j v := by
        unfold Parabolic.Family.envelopeDeficit at hz
        have hm : P.a i * (P.normalizedQuadratic i v - P.normalizedQuadratic j v) = 0 := by
          linarith
        rcases mul_eq_zero.mp hm with h | h
        · linarith
        · linarith
      exact ⟨hv.1, fun k => he ▸ hv.2 k⟩
    · intro hi
      have he : P.normalizedQuadratic i v = P.normalizedQuadratic j v :=
        le_antisymm (hi.2 j) (hv.2 i)
      unfold Parabolic.Family.envelopeDeficit
      rw [← he]
      linarith
  have hzero' : ∀ v ∈ seg j, P.envelopeDeficit i j v = 0 ↔ v ∈ seg i := by
    intro v hv
    rw [hcell j] at hv
    rw [hcell i, hzero v hv.1]
    exact ⟨fun h => ⟨h, hv.2⟩, fun h => h.1⟩
  refine ⟨hcell, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, (hzero' v hv).mp hz, hv⟩
  · rintro ⟨v, hi, hv⟩
    exact ⟨v, hv, (hzero' v hv).mpr hi⟩
  · rintro ⟨w, hi, hw⟩
    have hw' : w ∈ P.envelopeCell j := by rw [hcell j] at hw; exact hw.1
    have hd0 : P.envelopeDeficit i j w = 0 := (hzero' w hw).mpr hi
    have he0 : P.envelopeExponentDifference i j w = 0 :=
      P.envelopeExponentDifference_zero_of_deficit_zero hw' hd0
    set d₁ := P.a i * P.b j / P.a j - P.b i with hd₁
    set e₁ := -(P.a j - P.a i) / 2 * (P.b j / P.a j) with he₁
    have hd : ∀ v, P.envelopeDeficit i j v = (1 - P.a i / P.a j) + d₁ * v :=
      P.envelopeDeficit_affine i j
    have he : ∀ v, P.envelopeExponentDifference i j v =
        ((P.a j - P.a i) / 2 / P.a j + P.calibration j - P.calibration i) + e₁ * v :=
      P.envelopeExponentDifference_affine i j
    have h1 := hd w
    have h2 := he w
    rw [hd0] at h1
    rw [he0] at h2
    have hcross : ∀ v, P.envelopeExponentDifference i j v * d₁ =
        e₁ * P.envelopeDeficit i j v := by
      intro v
      rw [hd v, he v]
      linear_combination (-d₁) * h2 + e₁ * h1
    by_cases hz : d₁ = 0
    · refine ⟨0, fun v => ?_⟩
      rw [hz, zero_mul, add_zero] at h1
      have haij : P.a i = P.a j := by
        have hajpos := P.a_pos j
        have hq : P.a i / P.a j = 1 := by linarith
        rwa [div_eq_one_iff_eq hajpos.ne'] at hq
      have he1 : e₁ = 0 := by
        rw [he₁, haij]
        ring
      rw [he1, zero_mul, add_zero] at h2
      rw [he v, he1, zero_mul, add_zero, zero_mul]
      linarith
    · exact ⟨e₁ / d₁, fun v => by rw [div_mul_eq_mul_div, eq_div_iff hz]; exact hcross v⟩
  · intro hne hempty
    have hcont : Continuous (P.envelopeDeficit i j) := by
      have := P.normalizedQuadratic_continuous j
      unfold Parabolic.Family.envelopeDeficit
      fun_prop
    have hK : IsCompact (seg j) := by
      rw [hcell j]
      exact (P.envelopeCell_compact j).inter_right isClosed_Icc
    obtain ⟨v₀, hv₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
    have hv₀' : v₀ ∈ P.envelopeCell j := by rw [hcell j] at hv₀; exact hv₀.1
    have hpos : 0 < P.envelopeDeficit i j v₀ := by
      rcases (P.envelopeDeficit_nonneg i hv₀').lt_or_eq with h | h
      · exact h
      · have hmem : v₀ ∈ seg i ∩ seg j := ⟨(hzero' v₀ hv₀).mp h.symm, hv₀⟩
        rw [hempty] at hmem
        exact hmem.elim
    exact ⟨_, hpos, fun v hv => hmin hv⟩

/-- Item `C/10_Q/prose/027` (`companion/chapters/10_Q.tex:198`): "Removal of zero-length envelope
pieces avoids spurious triple junctions; it does not change the objective or its differentiable
gradients." After the removal (only essential pieces remain), no three distinct pieces are maximal
at a common normalized coordinate $\xi$; the pruned family has the same objective and, at every
differentiable point, the same gradient. -/
theorem no_triple_junction {m : ℕ} (P : Parabolic.Family m) :
    (∀ (ξ : ℝ) (i j k : Fin m), P.Essential i → P.Essential j → P.Essential k →
      P.ProfileActive i ξ → P.ProfileActive j ξ → P.ProfileActive k ξ → i = j ∨ j = k ∨ i = k) ∧
      (∀ x, P.prunedFamily.objective x = P.objective x) ∧
      (∀ x g, HasFDerivAt P.objective (gradientFunctional g) x →
        HasFDerivAt P.prunedFamily.objective (gradientFunctional g) x) := by
  have key : ∀ (ξ : ℝ) (p q r : Fin m), P.Canonical p → P.Essential q → P.Canonical r →
      p ≠ q → r ≠ q → P.b p < P.b q → P.b q < P.b r →
      P.ProfileActive p ξ → P.ProfileActive q ξ → P.ProfileActive r ξ → False := by
    intro ξ p q r hp hq hr hpq hrq hbpq hbqr hap haq har
    obtain ⟨_, ξ', hξ'⟩ := hq
    have h1 := hξ' p hp hpq
    have h2 := hξ' r hr hrq
    have e1 : P.profile p ξ = P.profile q ξ := le_antisymm (haq p) (hap q)
    have e2 : P.profile r ξ = P.profile q ξ := le_antisymm (haq r) (har q)
    simp only [Parabolic.Family.profile] at h1 h2 e1 e2
    have h3 : 0 < (P.b q - P.b p) * (ξ' - ξ) := by nlinarith
    have h4 : 0 < (P.b r - P.b q) * (ξ - ξ') := by nlinarith
    have h5 := (pos_iff_pos_of_mul_pos h3).mp (sub_pos.mpr hbpq)
    have h6 := (pos_iff_pos_of_mul_pos h4).mp (sub_pos.mpr hbqr)
    linarith
  refine ⟨fun ξ i j k hi hj hk hai haj hak => ?_, P.prunedFamily_objective,
    fun _ _ hg => P.prunedFamily_gradient hg⟩
  by_contra hne
  push_neg at hne
  obtain ⟨hij, hjk, hik⟩ := hne
  have bij : P.b i ≠ P.b j := fun h => hij (P.essential_slopes_injective hi hj h)
  have bjk : P.b j ≠ P.b k := fun h => hjk (P.essential_slopes_injective hj hk h)
  have bik : P.b i ≠ P.b k := fun h => hik (P.essential_slopes_injective hi hk h)
  rcases lt_or_gt_of_ne bij with h1 | h1 <;> rcases lt_or_gt_of_ne bjk with h2 | h2 <;>
    rcases lt_or_gt_of_ne bik with h3 | h3
  all_goals first
    | linarith
    | exact key ξ i j k hi.1 hj hk.1 hij hjk.symm (by assumption) (by assumption) hai haj hak
    | exact key ξ k j i hk.1 hj hi.1 hjk.symm hij (by assumption) (by assumption) hak haj hai
    | exact key ξ i k j hi.1 hk hj.1 hik hjk (by assumption) (by assumption) hai hak haj
    | exact key ξ j k i hj.1 hk hi.1 hjk hik (by assumption) (by assumption) haj hak hai
    | exact key ξ j i k hj.1 hi hk.1 hij.symm hik.symm (by assumption) (by assumption) haj hai hak
    | exact key ξ k i j hk.1 hi hj.1 hik.symm hij.symm (by assumption) (by assumption) hak hai haj

/-- Item `C/10_Q/disp/029` (`companion/chapters/10_Q.tex:201-203`): "It follows that the
compensated transport multiplier
\[ \widetilde\lambda=\theta(z)\lambda/\theta(x)" \]
is the library's `compensatedMultiplier x z` (a variable with this defining equation). -/
theorem compensated_def {m : ℕ} (P : Parabolic.Family m) (x z : Vec 2) (lt : ℝ)
    (hlt : lt = P.calibratedScale z * quotientMultiplier x z / P.calibratedScale x) :
    lt = P.compensatedMultiplier x z := hlt

/-- Item `C/10_Q/disp/030`, equation (10.17) (`companion/chapters/10_Q.tex:205-207`):
"[$\widetilde\lambda$] satisfies
\[ |\log\widetilde\lambda|\le C_\eta d." \]
On the band $\{\eta\le F\le B\}$ ($0\le c_1$, $c_2<1$): $C_\eta$ and $\delta$ chosen before the
pairs such that every eligible pair in the band with $d\le\delta$ has $D\ne0$, $\widetilde\lambda>0$
and the bound (library `exists_uniform_log_transport`). -/
theorem compensated_log {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (hη : 0 < η)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ x z g g' : Vec 2,
      η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
      EligiblePair P.objective c₁ c₂ x z g g' → pairDecrease x z g ≤ δ →
      stepDeterminant x z ≠ 0 ∧ 0 < P.compensatedMultiplier x z ∧
        |Real.log (P.compensatedMultiplier x z)| ≤ C * pairDecrease x z g := by
  obtain ⟨C, δ, hC, hδ, -, hb⟩ := P.exists_uniform_log_transport (band_compact P η B) hη hc₁ hc₂
  exact ⟨C, δ, hC, hδ, fun x z g g' hx hz hp hd => hb x hx z hz g g' hp hx.1 hz.1 hd⟩

/-- Item `C/10_Q/disp/031` (`companion/chapters/10_Q.tex:209-211`): "Because
\[ \Pi_s(\theta(z)r(z))=\widetilde\lambda\Pi_s(\theta(x)r(x)), \]"
with $\Pi_s$ the projector perpendicular to $s$ (`stepProjector`), whenever $D\ne0$. -/
theorem projected_transport {m : ℕ} (P : Parabolic.Family m) (x z : Vec 2)
    (hD : stepDeterminant x z ≠ 0) :
    stepProjector (pairStep x z) *ᵥ P.calibratedVector z =
      P.compensatedMultiplier x z • (stepProjector (pairStep x z) *ᵥ P.calibratedVector x) := by
  rw [P.calibrated_vector_transport hD, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    stepProjector_mulVec_self, smul_zero, add_zero]

/-- Item `C/10_Q/disp/032` (`companion/chapters/10_Q.tex:213-216`): "we obtain
\[ \Pi_sW(z)\Pi_s\preceq e^{2C_\eta d}\Pi_sW(x)\Pi_s\preceq(1+L_\eta d)\Pi_sW(x)\Pi_s \]
on a sufficiently small-decrease tail." With $W=(\theta r)(\theta r)^T$, on the band: $C_\eta$,
$L_\eta$ and $\delta$ chosen before the pairs such that, for every eligible pair in the band with
$d\le\delta$, both differences are positive semidefinite (Loewner order). -/
theorem transport_loewner {m : ℕ} (P : Parabolic.Family m) (η B : ℝ) (hη : 0 < η)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ C L δ : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ 0 < δ ∧ ∀ x z g g' : Vec 2,
      η ≤ P.objective x ∧ P.objective x ≤ B → η ≤ P.objective z ∧ P.objective z ≤ B →
      EligiblePair P.objective c₁ c₂ x z g g' → pairDecrease x z g ≤ δ →
      (Real.exp (2 * C * pairDecrease x z g) •
          (stepProjector (pairStep x z) * outer (P.calibratedVector x) (P.calibratedVector x) *
            stepProjector (pairStep x z)) -
        stepProjector (pairStep x z) * outer (P.calibratedVector z) (P.calibratedVector z) *
          stepProjector (pairStep x z)).PosSemidef ∧
      ((1 + L * pairDecrease x z g) •
          (stepProjector (pairStep x z) * outer (P.calibratedVector x) (P.calibratedVector x) *
            stepProjector (pairStep x z)) -
        Real.exp (2 * C * pairDecrease x z g) •
          (stepProjector (pairStep x z) * outer (P.calibratedVector x) (P.calibratedVector x) *
            stepProjector (pairStep x z))).PosSemidef := by
  obtain ⟨C, δ, hC, hδ, hδ1, hb⟩ := P.exists_uniform_log_transport (band_compact P η B) hη hc₁ hc₂
  have hL : 0 ≤ Real.exp (2 * C) - 1 := by
    have := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2 * C by positivity)
    rw [Real.exp_zero] at this; linarith
  refine ⟨C, Real.exp (2 * C) - 1, δ, hC.le, hL, hδ, fun x z g g' hx hz hp hd => ?_⟩
  obtain ⟨hD, hmul, hlog⟩ := hb x hx z hz g g' hp hx.1 hz.1 hd
  have hd0 := hp.decrease_pos.le
  set v := stepProjector (pairStep x z) *ᵥ P.calibratedVector x
  have hPz : stepProjector (pairStep x z) * outer (P.calibratedVector z) (P.calibratedVector z) *
      stepProjector (pairStep x z) = (P.compensatedMultiplier x z) ^ 2 • outer v v := by
    rw [projected_outer, projected_transport P x z hD]
    ext k l
    simp only [outer, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
    ring
  have hPx : stepProjector (pairStep x z) * outer (P.calibratedVector x) (P.calibratedVector x) *
      stepProjector (pairStep x z) = outer v v := projected_outer _ _
  rw [hPz, hPx, ← sub_smul, ← sub_smul]
  -- λ̃² ≤ e^{2Cd} ≤ 1 + (e^{2C} - 1)d
  have hsq : (P.compensatedMultiplier x z) ^ 2 ≤ Real.exp (2 * C * pairDecrease x z g) := by
    have hle : Real.log (P.compensatedMultiplier x z) ≤ C * pairDecrease x z g :=
      (le_abs_self _).trans hlog
    calc (P.compensatedMultiplier x z) ^ 2
        = Real.exp (2 * Real.log (P.compensatedMultiplier x z)) := by
          rw [show 2 * Real.log (P.compensatedMultiplier x z) =
            Real.log (P.compensatedMultiplier x z) + Real.log (P.compensatedMultiplier x z) by ring,
            Real.exp_add, Real.exp_log hmul]; ring
      _ ≤ Real.exp (2 * C * pairDecrease x z g) := Real.exp_le_exp.mpr (by nlinarith)
  have hexp : Real.exp (2 * C * pairDecrease x z g) ≤
      1 + (Real.exp (2 * C) - 1) * pairDecrease x z g :=
    exp_mul_le_one_add hd0 (hd.trans hδ1)
  refine ⟨DEmbedding.rankOne_posSemidef (by linarith) v,
    DEmbedding.rankOne_posSemidef (by linarith) v⟩

/-- Item `C/10_Q/prose/028` (`companion/chapters/10_Q.tex:217`): "This is (T). The
transported-certificate theorem of Chapter~\ref{comp:T} proves convergence from every admissible
initialization." (Wording point W26 applied on 15 October 2026; before "The general
theorem".) (V), (S) and (T) together: for every compact $K$, $\eta>0$, $0\le c_1$, $c_2<1$, the
field $W=(\theta r)(\theta r)^T$ is a band certificate (Definition `art:band-certificate`) on the
positive band of $K$ (library
`exists_bandCertificate`), and the certificate theorem then gives convergence of every admissible
run (`parabolic_convergence`). -/
theorem band_certificate {m : ℕ} (P : Parabolic.Family m) {K : Set (Vec 2)} (hK : IsCompact K)
    {η c₁ c₂ : ℝ} (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    (∃ Bc : BandCertificate P.objective K 0 c₁ c₂ η,
      ∀ x, Bc.W x = outer (P.calibratedVector x) (P.calibratedVector x)) ∧
      ∀ R : AdmissibleBFGSRun 2 P.objective,
        Tendsto (fun k => P.objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0) :=
  ⟨P.exists_bandCertificate hK hη hc₁ hc₂, fun R => R.parabolic_convergence P⟩

/-! ### The explicit three-branch example (`10_Q.tex:231-314`)

`Example.family` has $a=(1,3,2)$, $b=(1,0,-1)$ and `Example.objective` is its maximum (10.18).
`Example.oldPoint u ε` $=x_\epsilon=(u,2u^2+\epsilon)$, `Example.newPoint u ρ ε`
$=z_{\epsilon,\rho}=(u,2u^2-\rho\epsilon)$ (the printed $z_\epsilon$ is $\rho=1/2$),
`Example.initialMetric u A ρ ε` $=H_{\epsilon,\rho}$ (the printed $H_\epsilon$ is $\rho=1/2$),
`Example.oldGradient u` $=g=(2u,1)$ and `Example.newGradient u` $=g'=(6u,0)$; the printed scale
$\theta$ is `Example.sourceScale` and $\theta r$ is `Example.sourceVector`. -/

/-- Item `C/10_Q/disp/033`, equation (10.18) (`companion/chapters/10_Q.tex:233-235`): "Consider
\[ F(u,v)=\max\{u^2+v,\ 3u^2,\ 2u^2-v\}." \]
With $F$ a variable with this defining equation: $F$ is the library's `Example.objective`, the
maximum of the family `Example.family` with $a=(1,3,2)$ and $b=(1,0,-1)$. -/
theorem example_objective (F : Vec 2 → ℝ)
    (hF : ∀ x : Vec 2, F x = max (max ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)) (2 * (x 0) ^ 2 - x 1)) :
    F = Example.objective ∧ Example.objective = Example.family.objective ∧
      Example.family.a = ![1, 3, 2] ∧ Example.family.b = ![1, 0, -1] :=
  ⟨funext fun x => by rw [hF, Example.objective_eq_max], rfl, rfl, rfl⟩

/-- Item `C/10_Q/prose/029` (`companion/chapters/10_Q.tex:236`): "The switching parabolas are
$v=-u^2$ and $v=2u^2$." The branch $u^2+v$ is active exactly on $v\ge2u^2$, the branch $3u^2$
exactly on $-u^2\le v\le2u^2$, the branch $2u^2-v$ exactly on $v\le-u^2$; two different branches
are active at $(u,v)$ exactly when $v=2u^2$ or $v=-u^2$. -/
theorem example_switching :
    (∀ x : Vec 2, Example.family.Active 0 x ↔ 2 * (x 0) ^ 2 ≤ x 1) ∧
      (∀ x : Vec 2, Example.family.Active 1 x ↔ -(x 0) ^ 2 ≤ x 1 ∧ x 1 ≤ 2 * (x 0) ^ 2) ∧
      (∀ x : Vec 2, Example.family.Active 2 x ↔ x 1 ≤ -(x 0) ^ 2) ∧
      ∀ x : Vec 2, (∃ i j : Fin 3, i ≠ j ∧ Example.family.Active i x ∧ Example.family.Active j x) ↔
        (x 1 = 2 * (x 0) ^ 2 ∨ x 1 = -(x 0) ^ 2) := by
  have hmax : ∀ x : Vec 2, Example.family.objective x =
      max (max ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)) (2 * (x 0) ^ 2 - x 1) := Example.objective_eq_max
  have hb0 : ∀ x : Vec 2, Example.family.branch 0 x = (x 0) ^ 2 + x 1 := fun x => by
    simp [Parabolic.Family.branch, Example.family]
  have hb1 : ∀ x : Vec 2, Example.family.branch 1 x = 3 * (x 0) ^ 2 := fun x => by
    simp [Parabolic.Family.branch, Example.family]
  have hb2 : ∀ x : Vec 2, Example.family.branch 2 x = 2 * (x 0) ^ 2 - x 1 := fun x => by
    simp [Parabolic.Family.branch, Example.family, sub_eq_add_neg]
  have h0 : ∀ x : Vec 2, Example.family.Active 0 x ↔ 2 * (x 0) ^ 2 ≤ x 1 := by
    intro x
    unfold Parabolic.Family.Active
    rw [hmax, hb0]
    constructor
    · intro h
      have := le_max_right ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)
      have := le_max_left (max ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)) (2 * (x 0) ^ 2 - x 1)
      linarith
    · intro h
      exact le_antisymm (max_le (max_le le_rfl (by linarith)) (by linarith [sq_nonneg (x 0)]))
        ((le_max_left _ _).trans (le_max_left _ _))
  have h1 : ∀ x : Vec 2, Example.family.Active 1 x ↔ -(x 0) ^ 2 ≤ x 1 ∧ x 1 ≤ 2 * (x 0) ^ 2 := by
    intro x
    unfold Parabolic.Family.Active
    rw [hmax, hb1]
    constructor
    · intro h
      have := le_max_left ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)
      have := le_max_left (max ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)) (2 * (x 0) ^ 2 - x 1)
      have := le_max_right (max ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)) (2 * (x 0) ^ 2 - x 1)
      constructor <;> linarith
    · rintro ⟨h, h'⟩
      exact le_antisymm (max_le (max_le (by linarith) le_rfl) (by linarith))
        ((le_max_right _ _).trans (le_max_left _ _))
  have h2 : ∀ x : Vec 2, Example.family.Active 2 x ↔ x 1 ≤ -(x 0) ^ 2 := by
    intro x
    unfold Parabolic.Family.Active
    rw [hmax, hb2]
    constructor
    · intro h
      have := le_max_right ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)
      have := le_max_left (max ((x 0) ^ 2 + x 1) (3 * (x 0) ^ 2)) (2 * (x 0) ^ 2 - x 1)
      linarith
    · intro h
      exact le_antisymm (max_le (max_le (by linarith [sq_nonneg (x 0)]) (by linarith)) le_rfl)
        (le_max_right _ _)
  refine ⟨h0, h1, h2, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hc : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    have s := sq_nonneg (x 0)
    rcases hc i with rfl | rfl | rfl <;> rcases hc j with rfl | rfl | rfl
    · exact absurd rfl hij
    · have a := (h0 x).mp hi
      have b := (h1 x).mp hj
      left; linarith [b.2]
    · have a := (h0 x).mp hi
      have b := (h2 x).mp hj
      left; linarith
    · have a := (h1 x).mp hi
      have b := (h0 x).mp hj
      left; linarith [a.2]
    · exact absurd rfl hij
    · have a := (h1 x).mp hi
      have b := (h2 x).mp hj
      right; linarith [a.1]
    · have a := (h2 x).mp hi
      have b := (h0 x).mp hj
      left; linarith
    · have a := (h2 x).mp hi
      have b := (h1 x).mp hj
      right; linarith [b.1]
    · exact absurd rfl hij
  · rintro (h | h)
    · exact ⟨0, 1, by decide, (h0 x).mpr h.ge, (h1 x).mpr ⟨by linarith [sq_nonneg (x 0)], h.le⟩⟩
    · exact ⟨1, 2, by decide, (h1 x).mpr ⟨h.ge, by linarith [sq_nonneg (x 0)]⟩, (h2 x).mpr h.le⟩

/-- Item `C/10_Q/prose/030` (`companion/chapters/10_Q.tex:236`): "Between them the objective is
flat in $v$, but the origin is its unique minimizer." On $-u^2\le v\le2u^2$ the objective is
$3u^2$, independent of $v$ (with $v$-derivative $0$ on the open region); $F(0)=0<F(x)$ for
$x\ne0$. -/
theorem example_flat_unique :
    (∀ x : Vec 2, -(x 0) ^ 2 ≤ x 1 → x 1 ≤ 2 * (x 0) ^ 2 → Example.objective x = 3 * (x 0) ^ 2) ∧
      (∀ x : Vec 2, -(x 0) ^ 2 < x 1 → x 1 < 2 * (x 0) ^ 2 →
        HasFDerivAt Example.objective (gradientFunctional ![6 * x 0, 0]) x) ∧
      Example.objective 0 = 0 ∧ ∀ x : Vec 2, x ≠ 0 → Example.objective 0 < Example.objective x := by
  have h0 : Example.objective 0 = 0 := Example.family.objective_zero
  refine ⟨fun x h1 h2 => Example.objective_middle_closed h1 h2,
    fun x h1 h2 => Example.middle_hasGradient h1 h2, h0, fun x hx => ?_⟩
  rw [h0]
  exact lt_of_le_of_ne (Example.family.objective_nonneg x)
    (fun h => hx (Example.family.unique_zero x h.symm))

/-- Item `C/10_Q/prose/031` (`companion/chapters/10_Q.tex:236`): "The theorem applies globally."
The coefficients $a=(1,3,2)$, $b=(1,0,-1)$ satisfy the hypotheses of Theorem `theorem/001`, and
`parabolic_convergence`, applied to them, gives convergence of every admissible run, from every
initial point and every $H_0\succ0$. -/
theorem example_applies :
    (∀ i, 0 < (![1, 3, 2] : Fin 3 → ℝ) i) ∧ (∃ i, (![1, 0, -1] : Fin 3 → ℝ) i < 0) ∧
      (∃ i, 0 < (![1, 0, -1] : Fin 3 → ℝ) i) ∧
      ∀ R : AdmissibleBFGSRun 2 Example.objective,
        Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => Example.objective (R.x k)) atTop (𝓝 0) := by
  have ha : ∀ i, 0 < (![1, 3, 2] : Fin 3 → ℝ) i := Example.family.a_pos
  have hneg : ∃ i, (![1, 0, -1] : Fin 3 → ℝ) i < 0 := Example.family.negative_slope
  have hpos : ∃ i, 0 < (![1, 0, -1] : Fin 3 → ℝ) i := Example.family.positive_slope
  exact ⟨ha, hneg, hpos, fun R => parabolic_convergence _ _ ha hneg hpos Example.objective
    (objective_isGreatest Example.family) R⟩

/-- Item `C/10_Q/disp/034` (`companion/chapters/10_Q.tex:239-246`), with the lead-in of line 238:
"An especially simple scaling for (10.8) is
\[ \theta(u,v)=\begin{cases}\exp\{u^2/F-1/3\},&v<-u^2,\\ 1,&-u^2<v<2u^2,\\
   \exp\{u^2/(2F)-1/6\},&v>2u^2.\end{cases} \]"
$\theta$ is a variable with these defining equations on the three open regions. Off the two
interfaces it is the library's `Example.sourceScale`; it has the form (10.8),
$\theta=\exp\{a_iu^2/(2F)+k_i\}$ with the active branch $i$, for $k=(-1/6,-1/2,-1/3)$ (branches
$u^2+v$, $3u^2$, $2u^2-v$); these constants satisfy the recursion (10.7) along the branches ordered
by increasing slope ($2u^2-v$, $3u^2$, $u^2+v$: breakpoints $\xi=-1$ and $\xi=2$, both with $A=3$);
they differ from the library's `calibration` by one common constant, so on $F>0$ the scale is the
library's calibrated scale times the positive constant `sourceNormalization`. -/
theorem example_scale (θ : Vec 2 → ℝ)
    (hθ₁ : ∀ x : Vec 2, x 1 < -(x 0) ^ 2 →
      θ x = Real.exp ((x 0) ^ 2 / Example.objective x - 1 / 3))
    (hθ₂ : ∀ x : Vec 2, -(x 0) ^ 2 < x 1 → x 1 < 2 * (x 0) ^ 2 → θ x = 1)
    (hθ₃ : ∀ x : Vec 2, 2 * (x 0) ^ 2 < x 1 →
      θ x = Real.exp ((x 0) ^ 2 / (2 * Example.objective x) - 1 / 6))
    (k : Fin 3 → ℝ) (hk : k = ![-1 / 6, -1 / 2, -1 / 3]) :
    (∀ x : Vec 2, x 1 ≠ -(x 0) ^ 2 → x 1 ≠ 2 * (x 0) ^ 2 → θ x = Example.sourceScale x) ∧
      (∀ x : Vec 2, x 1 ≠ -(x 0) ^ 2 → x 1 ≠ 2 * (x 0) ^ 2 → ∀ i, Example.family.Active i x →
        θ x = Real.exp (Example.family.a i * (x 0) ^ 2 / (2 * Example.objective x) + k i)) ∧
      (Example.family.breakpoint 2 1 = -1 ∧ Example.family.breakpoint 1 0 = 2 ∧
        Example.family.a 2 + Example.family.b 2 * (-1) = 3 ∧
        Example.family.a 1 + Example.family.b 1 * 2 = 3 ∧
        k 1 - k 2 = -(Example.family.a 1 - Example.family.a 2) / (2 * 3) ∧
        k 0 - k 1 = -(Example.family.a 0 - Example.family.a 1) / (2 * 3)) ∧
      (∀ i, k i = Example.family.calibration i - (Example.family.calibration 1 + 1 / 2)) ∧
      ∀ x : Vec 2, 0 < Example.objective x →
        Example.sourceScale x = Example.sourceNormalization * Example.family.calibratedScale x := by
  obtain ⟨hA0, hA1, hA2, -⟩ := example_switching
  have hc : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have ha0 : Example.family.a 0 = 1 := rfl
  have ha1 : Example.family.a 1 = 3 := rfl
  have ha2 : Example.family.a 2 = 2 := rfl
  have hb0 : Example.family.b 0 = 1 := rfl
  have hb1 : Example.family.b 1 = 0 := rfl
  have hb2 : Example.family.b 2 = -1 := rfl
  have hk0 : k 0 = -1 / 6 := by rw [hk]; rfl
  have hk1 : k 1 = -1 / 2 := by rw [hk]; rfl
  have hk2 : k 2 = -1 / 3 := by rw [hk]; rfl
  -- the three open regions
  have hreg : ∀ x : Vec 2, x 1 ≠ -(x 0) ^ 2 → x 1 ≠ 2 * (x 0) ^ 2 →
      x 1 < -(x 0) ^ 2 ∨ (-(x 0) ^ 2 < x 1 ∧ x 1 < 2 * (x 0) ^ 2) ∨ 2 * (x 0) ^ 2 < x 1 := by
    intro x h1 h2
    rcases lt_or_gt_of_ne h1 with h | h
    · exact Or.inl h
    · rcases lt_or_gt_of_ne h2 with h' | h'
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr h')
  have hsq := fun x : Vec 2 => sq_nonneg (x 0)
  refine ⟨fun x h1 h2 => ?_, fun x h1 h2 i hi => ?_, ?_, fun i => ?_,
    fun x hx => Example.sourceScale_eq_normalized hx⟩
  · rcases hreg x h1 h2 with h | ⟨h, h'⟩ | h
    · rw [hθ₁ x h, Example.sourceScale, if_pos h]
    · rw [hθ₂ x h h', Example.sourceScale, if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h'.le)]
    · rw [hθ₃ x h, Example.sourceScale, if_neg (by linarith [hsq x]), if_pos h]
  · rcases hreg x h1 h2 with h | ⟨h, h'⟩ | h
    · have hi2 : i = 2 := by
        rcases hc i with rfl | rfl | rfl
        · exact absurd ((hA0 x).mp hi) (by linarith [hsq x])
        · exact absurd ((hA1 x).mp hi).1 (by linarith)
        · rfl
      subst hi2
      rw [hθ₁ x h, ha2, hk2]
      congr 1
      ring
    · have hi1 : i = 1 := by
        rcases hc i with rfl | rfl | rfl
        · exact absurd ((hA0 x).mp hi) (by linarith)
        · rfl
        · exact absurd ((hA2 x).mp hi) (by linarith)
      subst hi1
      have hu : (x 0) ^ 2 ≠ 0 := by
        intro h0
        rw [h0] at h h'
        linarith
      rw [hθ₂ x h h', ha1, hk1, Example.objective_middle_closed h.le h'.le]
      have he : 3 * (x 0) ^ 2 / (2 * (3 * (x 0) ^ 2)) + -1 / 2 = 0 := by
        rw [div_add' _ _ _ (mul_ne_zero two_ne_zero (mul_ne_zero three_ne_zero hu)),
          div_eq_zero_iff]
        left
        ring
      rw [he, Real.exp_zero]
    · have hi0 : i = 0 := by
        rcases hc i with rfl | rfl | rfl
        · rfl
        · exact absurd ((hA1 x).mp hi).2 (by linarith)
        · exact absurd ((hA2 x).mp hi) (by linarith [hsq x])
      subst hi0
      rw [hθ₃ x h, ha0, hk0, one_mul]
      congr 1
      ring
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Parabolic.Family.breakpoint, ha1, ha2, hb1, hb2]
      norm_num
    · simp only [Parabolic.Family.breakpoint, ha0, ha1, hb0, hb1]
      norm_num
    · rw [ha2, hb2]
      norm_num
    · rw [ha1, hb1]
      norm_num
    · rw [hk1, hk2, ha1, ha2]
      norm_num
    · rw [hk0, hk1, ha0, ha1]
      norm_num
  · obtain ⟨hc0, hc2⟩ := Example.calibration_differences
    rcases hc i with rfl | rfl | rfl
    · rw [hk0, hc0]
      ring
    · rw [hk1]
      ring
    · rw [hk2, hc2]
      ring

/-- Item `C/10_Q/prose/033` (`companion/chapters/10_Q.tex:247`): "It is continuous across both
interfaces, and $e^{-1/3}\le\theta\le1$." The scale extended across the interfaces
(`Example.sourceScale`, equal to $\theta$ off the interfaces by `example_scale`) is continuous on
$F>0$; on each interface ($u\ne0$) the formula of the outer region takes the middle value $1$; and
$e^{-1/3}\le\theta\le1$ on $F>0$. -/
theorem example_scale_continuous :
    ContinuousOn Example.sourceScale {x | 0 < Example.objective x} ∧
      (∀ x : Vec 2, x 0 ≠ 0 → x 1 = -(x 0) ^ 2 →
        Real.exp ((x 0) ^ 2 / Example.objective x - 1 / 3) = 1 ∧ Example.sourceScale x = 1) ∧
      (∀ x : Vec 2, x 0 ≠ 0 → x 1 = 2 * (x 0) ^ 2 →
        Real.exp ((x 0) ^ 2 / (2 * Example.objective x) - 1 / 6) = 1 ∧
          Example.sourceScale x = 1) ∧
      ∀ x : Vec 2, 0 < Example.objective x →
        Real.exp (-1 / 3) ≤ Example.sourceScale x ∧ Example.sourceScale x ≤ 1 := by
  refine ⟨Example.sourceScale_continuousOn, fun x hx h => ?_, fun x hx h => ?_,
    fun x hx => Example.sourceScale_bounds hx⟩
  · have hu : (x 0) ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hF : Example.objective x = 3 * (x 0) ^ 2 :=
      Example.objective_middle_closed h.ge (by rw [h]; nlinarith [sq_nonneg (x 0)])
    refine ⟨?_, ?_⟩
    · rw [hF, div_mul_cancel_right₀ hu, show (3 : ℝ)⁻¹ - 1 / 3 = 0 by norm_num, Real.exp_zero]
    · rw [Example.sourceScale, if_neg (by rw [h]; exact lt_irrefl _),
        if_neg (by rw [h]; nlinarith [sq_nonneg (x 0)])]
  · have hu : (x 0) ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hF : Example.objective x = 3 * (x 0) ^ 2 :=
      Example.objective_middle_closed (by rw [h]; nlinarith [sq_nonneg (x 0)]) h.le
    refine ⟨?_, ?_⟩
    · rw [hF, show 2 * (3 * (x 0) ^ 2) = 6 * (x 0) ^ 2 by ring, div_mul_cancel_right₀ hu,
        show (6 : ℝ)⁻¹ - 1 / 6 = 0 by norm_num, Real.exp_zero]
    · rw [Example.sourceScale, if_neg (by rw [h]; nlinarith [sq_nonneg (x 0)]),
        if_neg (by rw [h]; exact lt_irrefl _)]

/-- Item `C/10_Q/prose/034` (`companion/chapters/10_Q.tex:247`): "Take
$W=\theta^2(u,2v)(u,2v)^T$." With $W$ a variable with this defining equation ($\theta$ the scale
extended across the interfaces): $W=(\theta r)(\theta r)^T$ and, as in the general case, it is a
band certificate on every compact set and positive band (library
`exists_source_bandCertificate`). -/
theorem example_field (W : Vec 2 → Mat 2)
    (hW : ∀ x : Vec 2, W x = (Example.sourceScale x) ^ 2 • outer ![x 0, 2 * x 1] ![x 0, 2 * x 1]) :
    (∀ x, W x = outer (Example.sourceVector x) (Example.sourceVector x)) ∧
      ∀ K : Set (Vec 2), IsCompact K → ∀ η c₁ c₂ : ℝ, 0 < η → 0 ≤ c₁ → c₂ < 1 →
        ∃ Bc : BandCertificate Example.objective K 0 c₁ c₂ η, ∀ x, Bc.W x = W x := by
  have hW' : ∀ x, W x = outer (Example.sourceVector x) (Example.sourceVector x) := by
    intro x
    rw [hW x]
    ext k l
    simp only [Example.sourceVector, outer, radialDirection, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  refine ⟨hW', fun K hK η c₁ c₂ hη hc₁ hc₂ => ?_⟩
  obtain ⟨Bc, hBc⟩ := Example.exists_source_bandCertificate hK hη hc₁ hc₂
  exact ⟨Bc, fun x => by rw [hBc, hW']⟩

/-- Item `C/10_Q/disp/035` (`companion/chapters/10_Q.tex:250-253`), with the standing assumptions
of line 249: "Fix $u\ne0$, $A>0$, and $0<\epsilon<6u^2$. Let
\[ x_\epsilon=(u,2u^2+\epsilon),\qquad z_\epsilon=(u,2u^2-\epsilon/2), \]"
variables with these defining equations: they are `Example.oldPoint u ε` and
`Example.newPoint u (1/2) ε`. -/
theorem printed_points (u A ε : ℝ) (_hu : u ≠ 0) (_hA : 0 < A) (_hε : 0 < ε)
    (_hεu : ε < 6 * u ^ 2) (x z : Vec 2) (hx : x = ![u, 2 * u ^ 2 + ε])
    (hz : z = ![u, 2 * u ^ 2 - ε / 2]) :
    x = Example.oldPoint u ε ∧ z = Example.newPoint u (1 / 2) ε := by
  refine ⟨hx, ?_⟩
  rw [hz]
  ext i
  fin_cases i
  · rfl
  · show 2 * u ^ 2 - ε / 2 = 2 * u ^ 2 - 1 / 2 * ε
    ring

/-- Item `C/10_Q/disp/036` (`companion/chapters/10_Q.tex:254-259`):
\[ H_\epsilon=\begin{pmatrix}A&-2uA\\-2uA&4u^2A+3\epsilon/2\end{pmatrix}\succ0. \]
$H_\epsilon$ is a variable with this defining equation; it is `Example.initialMetric u A (1/2) ε`
and it is positive definite ($A>0$, $\epsilon>0$). -/
theorem printed_metric (u A ε : ℝ) (_hu : u ≠ 0) (hA : 0 < A) (hε : 0 < ε)
    (_hεu : ε < 6 * u ^ 2) (H : Mat 2)
    (hH : H = !![A, -2 * u * A; -2 * u * A, 4 * u ^ 2 * A + 3 * ε / 2]) :
    H = Example.initialMetric u A (1 / 2) ε ∧ H.PosDef := by
  have he : H = Example.initialMetric u A (1 / 2) ε := by
    rw [hH]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · show 4 * u ^ 2 * A + 3 * ε / 2 = 4 * u ^ 2 * A + (1 + 1 / 2) * ε
      ring
  exact ⟨he, he ▸ Example.initialMetric_posDef hA (by norm_num) hε⟩

/-- Item `C/10_Q/disp/041` (`companion/chapters/10_Q.tex:290-293`), with the claim of line 289 "The
active gradients remain $(2u,1)^T$ and $(6u,0)^T$, and direct calculation gives
\[ -H_{\epsilon,\rho}g=z_{\epsilon,\rho}-x_\epsilon,\qquad d=t=(1+\rho)\epsilon,
   \qquad\Delta=\epsilon." \]
For $\rho>0$, $\epsilon>0$, $\rho\epsilon<3u^2$ and every $A$. -/
theorem family_identities (u A ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) (hs : ρ * ε < 3 * u ^ 2) :
    HasFDerivAt Example.objective (gradientFunctional ![2 * u, 1]) (Example.oldPoint u ε) ∧
      HasFDerivAt Example.objective (gradientFunctional ![6 * u, 0]) (Example.newPoint u ρ ε) ∧
      -(Example.initialMetric u A ρ ε *ᵥ ![2 * u, 1]) =
        Example.newPoint u ρ ε - Example.oldPoint u ε ∧
      pairDecrease (Example.oldPoint u ε) (Example.newPoint u ρ ε) ![2 * u, 1] = (1 + ρ) * ε ∧
      pairCurvature (Example.oldPoint u ε) (Example.newPoint u ρ ε) ![2 * u, 1] ![6 * u, 0] =
        (1 + ρ) * ε ∧
      Example.objective (Example.oldPoint u ε) - Example.objective (Example.newPoint u ρ ε) =
        ε := by
  obtain ⟨hg, hg'⟩ := Example.pair_gradients hρ hε hs
  obtain ⟨hx, hz⟩ := Example.pair_values hρ hε hs
  have hstep := Example.initialMetric_step u A ρ ε
  rw [bfgsStep, neg_smul, one_smul] at hstep
  exact ⟨hg, hg', hstep, Example.pair_decrease u ρ ε, Example.pair_curvature u ρ ε,
    by rw [hx, hz]; ring⟩

/-- Item `C/10_Q/disp/037` (`companion/chapters/10_Q.tex:261-264`), with the claim of line 260 "The
gradients are $g=(2u,1)^T$ and $g'=(6u,0)^T$. Directly,
\[ -H_\epsilon g=z_\epsilon-x_\epsilon,\quad d=t=3\epsilon/2,\quad \Delta=\epsilon." \]
Under the standing assumptions of line 249 ($A$ is not used). -/
theorem printed_identities (u A ε : ℝ) (_hu : u ≠ 0) (_hA : 0 < A) (hε : 0 < ε)
    (hεu : ε < 6 * u ^ 2) :
    HasFDerivAt Example.objective (gradientFunctional ![2 * u, 1]) (Example.oldPoint u ε) ∧
      HasFDerivAt Example.objective (gradientFunctional ![6 * u, 0])
        (Example.newPoint u (1 / 2) ε) ∧
      -(Example.initialMetric u A (1 / 2) ε *ᵥ ![2 * u, 1]) =
        Example.newPoint u (1 / 2) ε - Example.oldPoint u ε ∧
      pairDecrease (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) ![2 * u, 1] = 3 * ε / 2 ∧
      pairCurvature (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) ![2 * u, 1]
        ![6 * u, 0] = 3 * ε / 2 ∧
      Example.objective (Example.oldPoint u ε) - Example.objective (Example.newPoint u (1 / 2) ε) =
        ε := by
  obtain ⟨hg, hg', hstep, hd, ht, hΔ⟩ :=
    family_identities u A (1 / 2) ε (by norm_num) hε (by linarith)
  exact ⟨hg, hg', hstep, by rw [hd]; ring, by rw [ht]; ring, hΔ⟩

/-- Item `C/10_Q/prose/036` (`companion/chapters/10_Q.tex:265`): "Under the fixed ordinary
line-search parameters, $\alpha=1$ is an actual first full-BFGS step exactly when the Armijo
condition $c_1\le2/3$ holds." For $0<c_1<c_2<1$ and the standing assumptions of line 249:
$H_\epsilon$ is positive definite, the unit step from $x_\epsilon$ along $-H_\epsilon g$ lands at
$z_\epsilon$, $F$ is differentiable at both points with the gradients $g$, $g'$, and the Armijo and
weak Wolfe conditions of `AdmissibleBFGSRun` (with $\alpha=1$) hold together exactly when
$c_1\le2/3$. -/
theorem printed_acceptance (u A ε c₁ c₂ : ℝ) (_hu : u ≠ 0) (hA : 0 < A) (hε : 0 < ε)
    (hεu : ε < 6 * u ^ 2) (_hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1) :
    (Example.initialMetric u A (1 / 2) ε).PosDef ∧
      Example.oldPoint u ε + bfgsStep (Example.initialMetric u A (1 / 2) ε)
        (Example.oldGradient u) 1 = Example.newPoint u (1 / 2) ε ∧
      HasFDerivAt Example.objective (gradientFunctional (Example.oldGradient u))
        (Example.oldPoint u ε) ∧
      HasFDerivAt Example.objective (gradientFunctional (Example.newGradient u))
        (Example.newPoint u (1 / 2) ε) ∧
      ((Example.objective (Example.newPoint u (1 / 2) ε) ≤
          Example.objective (Example.oldPoint u ε) +
          c₁ * dot (Example.oldGradient u)
            (bfgsStep (Example.initialMetric u A (1 / 2) ε) (Example.oldGradient u) 1) ∧
        c₂ * dot (Example.oldGradient u)
            (bfgsStep (Example.initialMetric u A (1 / 2) ε) (Example.oldGradient u) 1) ≤
          dot (Example.newGradient u)
            (bfgsStep (Example.initialMetric u A (1 / 2) ε) (Example.oldGradient u) 1)) ↔
        c₁ ≤ 2 / 3) := by
  have hs : 1 / 2 * ε < 3 * u ^ 2 := by linarith
  obtain ⟨hg, hg'⟩ := Example.pair_gradients (by norm_num : (0 : ℝ) < 1 / 2) hε hs
  have hstep := Example.initialMetric_step u A (1 / 2) ε
  rw [hstep]
  have hwolfe := (Example.strict_weak_wolfe (u := u) (c₂ := c₂) (by norm_num : (0 : ℝ) < 1 / 2) hε
    (by linarith)).le
  have harm := Example.printed_armijo_iff (c₁ := c₁) hε hεu
  have hdec : pairDecrease (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)
      (Example.oldGradient u) = -dot (Example.oldGradient u)
        (pairStep (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)) := rfl
  refine ⟨Example.initialMetric_posDef hA (by norm_num) hε, by rw [pairStep]; abel, hg, hg', ?_⟩
  rw [hdec] at harm
  constructor
  · rintro ⟨h1, -⟩
    exact harm.mp (by linarith)
  · intro h
    exact ⟨by linarith [harm.mpr h], hwolfe⟩

/-- Item `C/10_Q/prose/037` (`companion/chapters/10_Q.tex:265`): "Armijo is strict for $c_1<2/3$,
and weak Wolfe is strict for every allowed $c_2>0$." For the unit step
$s=-H_\epsilon g=z_\epsilon-x_\epsilon$ under the standing assumptions of line 249. -/
theorem printed_strict (u A ε c₁ c₂ : ℝ) (_hu : u ≠ 0) (_hA : 0 < A) (hε : 0 < ε)
    (hεu : ε < 6 * u ^ 2) :
    (c₁ < 2 / 3 → Example.objective (Example.newPoint u (1 / 2) ε) <
        Example.objective (Example.oldPoint u ε) + c₁ * dot (Example.oldGradient u)
          (bfgsStep (Example.initialMetric u A (1 / 2) ε) (Example.oldGradient u) 1)) ∧
      (0 < c₂ → c₂ * dot (Example.oldGradient u)
          (bfgsStep (Example.initialMetric u A (1 / 2) ε) (Example.oldGradient u) 1) <
        dot (Example.newGradient u)
          (bfgsStep (Example.initialMetric u A (1 / 2) ε) (Example.oldGradient u) 1)) := by
  rw [Example.initialMetric_step u A (1 / 2) ε]
  refine ⟨fun hc₁ => ?_, fun hc₂ => (Example.printed_strict_acceptance (c₁ := 0) hε hεu
    (by norm_num) hc₂).2⟩
  have h := (Example.printed_strict_acceptance (c₂ := 1) hε hεu hc₁ one_pos).1
  have hdec : pairDecrease (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)
      (Example.oldGradient u) = -dot (Example.oldGradient u)
        (pairStep (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)) := rfl
  rw [hdec] at h
  linarith

/-- Item `C/10_Q/disp/042` (`companion/chapters/10_Q.tex:295-299`): "Their radial quotient is
\[ \frac{(y^Tz_{\epsilon,\rho})^2}{t}
   =\frac{(2u^2+\rho\epsilon)^2}{(1+\rho)\epsilon}\longrightarrow\infty." \]
$y=g'-g$; $y^Tz_{\epsilon,\rho}=y^T(z_{\epsilon,\rho}-0)$ is the radial numerator of (RS) at
$x_*=0$; the limit is $\epsilon\downarrow0$ with $u\ne0$ and $\rho>0$ fixed. -/
theorem family_radial (u ρ : ℝ) (hu : u ≠ 0) (hρ : 0 < ρ) :
    (∀ ε, (dot (Example.newGradient u - Example.oldGradient u) (Example.newPoint u ρ ε)) ^ 2 /
        pairCurvature (Example.oldPoint u ε) (Example.newPoint u ρ ε) (Example.oldGradient u)
          (Example.newGradient u) = (2 * u ^ 2 + ρ * ε) ^ 2 / ((1 + ρ) * ε)) ∧
      Tendsto (fun ε => (dot (Example.newGradient u - Example.oldGradient u)
          (Example.newPoint u ρ ε)) ^ 2 /
        pairCurvature (Example.oldPoint u ε) (Example.newPoint u ρ ε) (Example.oldGradient u)
          (Example.newGradient u)) (𝓝[>] 0) atTop := by
  have hnum : ∀ ε, dot (Example.newGradient u - Example.oldGradient u) (Example.newPoint u ρ ε) =
      2 * u ^ 2 + ρ * ε := fun ε => by
    have h := Example.radial_numerator u ρ ε
    simpa only [RadialCertificate.radialNumerator, sub_zero] using h
  refine ⟨fun ε => by rw [hnum, Example.pair_curvature], ?_⟩
  simpa only [RadialCertificate.radialNumerator, sub_zero] using
    Example.radial_quotient_tendsto hu hρ

/-- Item `C/10_Q/disp/038` (`companion/chapters/10_Q.tex:268-271`), with the claim of line 267:
"Here $y=(4u,-1)^T$, so
\[ \frac{(y^Tz_\epsilon)^2}{t}=\frac{(2u^2+\epsilon/2)^2}{3\epsilon/2}\longrightarrow\infty." \]
$y=g'-g$; the limit is $\epsilon\downarrow0$ with $u\ne0$ fixed. -/
theorem printed_radial (u : ℝ) (hu : u ≠ 0) :
    Example.newGradient u - Example.oldGradient u = ![4 * u, -1] ∧
      (∀ ε, (dot (Example.newGradient u - Example.oldGradient u)
          (Example.newPoint u (1 / 2) ε)) ^ 2 /
        pairCurvature (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) (Example.oldGradient u)
          (Example.newGradient u) = (2 * u ^ 2 + ε / 2) ^ 2 / (3 * ε / 2)) ∧
      Tendsto (fun ε => (dot (Example.newGradient u - Example.oldGradient u)
          (Example.newPoint u (1 / 2) ε)) ^ 2 /
        pairCurvature (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) (Example.oldGradient u)
          (Example.newGradient u)) (𝓝[>] 0) atTop := by
  obtain ⟨h1, h2⟩ := family_radial u (1 / 2) hu (by norm_num)
  refine ⟨?_, fun ε => by rw [h1]; congr 1 <;> ring, h2⟩
  ext i
  fin_cases i
  · show 6 * u - 2 * u = 4 * u
    ring
  · show (0 : ℝ) - 1 = -1
    ring

/-- Item `C/10_Q/prose/040` (`companion/chapters/10_Q.tex:272`): "The values tend to the positive
level $3u^2$ while $d\to0$." As $\epsilon\downarrow0$, with $u\ne0$ fixed. -/
theorem printed_limits (u : ℝ) (hu : u ≠ 0) :
    0 < 3 * u ^ 2 ∧
      Tendsto (fun ε => Example.objective (Example.oldPoint u ε)) (𝓝[>] 0) (𝓝 (3 * u ^ 2)) ∧
      Tendsto (fun ε => Example.objective (Example.newPoint u (1 / 2) ε)) (𝓝[>] 0)
        (𝓝 (3 * u ^ 2)) ∧
      Tendsto (fun ε => pairDecrease (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)
        (Example.oldGradient u)) (𝓝[>] 0) (𝓝 0) :=
  ⟨mul_pos (by norm_num) (sq_pos_of_ne_zero hu), (Example.pair_values_tendsto u (1 / 2)).1,
    (Example.pair_values_tendsto u (1 / 2)).2, Example.pair_decrease_tendsto u (1 / 2)⟩

/-- Item `C/10_Q/prose/041` (`companion/chapters/10_Q.tex:272`): "Such pairs exist in every
neighborhood of zero, with $u\ne0$ fixed before taking $\epsilon\downarrow0$." For every
neighborhood $K$ of $0$ there is $u\ne0$ such that, for all sufficiently small $\epsilon>0$,
$\epsilon<6u^2$ and both points of the pair lie in $K$. -/
theorem printed_every_neighborhood {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    ∃ u : ℝ, u ≠ 0 ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε < 6 * u ^ 2 ∧ Example.oldPoint u ε ∈ K ∧ Example.newPoint u (1 / 2) ε ∈ K := by
  obtain ⟨u, hu, hKu⟩ := Example.exists_nonzero_base_in_neighborhood hK
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 6 * u ^ 2 :=
    (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds (mul_pos (by norm_num) (sq_pos_of_ne_zero hu)))
  refine ⟨u, hu, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hsmall,
    (Example.pair_points_tendsto u (1 / 2)).1.eventually hKu,
    (Example.pair_points_tendsto u (1 / 2)).2.eventually hKu] with ε h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

/-- Item `C/10_Q/disp/039` (`companion/chapters/10_Q.tex:275-278`), for a fixed ordinary pair
$0<c_1<c_2<1$: "Choose
\[ \rho=\frac{1-c_1}{2c_1}>0,\qquad c_1(1+\rho)=\frac{1+c_1}{2}<1," \]
$\rho$ a variable with its defining equation. -/
theorem rho_choice (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) (ρ : ℝ)
    (hρ : ρ = (1 - c₁) / (2 * c₁)) :
    0 < ρ ∧ c₁ * (1 + ρ) = (1 + c₁) / 2 ∧ (1 + c₁) / 2 < 1 := by
  subst hρ
  refine ⟨div_pos (by linarith) (by linarith), ?_, by linarith⟩
  field_simp
  ring

/-- Item `C/10_Q/disp/040` (`companion/chapters/10_Q.tex:280-287`): "replace the new point and
metric by
\[ z_{\epsilon,\rho}=(u,2u^2-\rho\epsilon),\qquad
   H_{\epsilon,\rho}=\begin{pmatrix}A&-2uA\\-2uA&4u^2A+(1+\rho)\epsilon
   \end{pmatrix},\qquad0<\rho\epsilon<3u^2." \]
Variables with these defining equations (the last condition is a standing assumption): they are
`Example.newPoint u ρ ε` and `Example.initialMetric u A ρ ε`. -/
theorem family_pair_def (u A ρ ε : ℝ) (_hρε : 0 < ρ * ε) (_hρε' : ρ * ε < 3 * u ^ 2)
    (z : Vec 2) (H : Mat 2) (hz : z = ![u, 2 * u ^ 2 - ρ * ε])
    (hH : H = !![A, -2 * u * A; -2 * u * A, 4 * u ^ 2 * A + (1 + ρ) * ε]) :
    z = Example.newPoint u ρ ε ∧ H = Example.initialMetric u A ρ ε :=
  ⟨hz, hH⟩

/-- Item `C/10_Q/prose/043` (`companion/chapters/10_Q.tex:288-289`): "For any $A>0$, the quadratic
form is $A(w_1-2uw_2)^2+(1+\rho)\epsilon w_2^2$, so the metric is SPD." ($w_1,w_2$ are `w 0`, `w 1`;
$\rho>0$, $\epsilon>0$.) -/
theorem family_metric (u A ρ ε : ℝ) (hA : 0 < A) (hρ : 0 < ρ) (hε : 0 < ε) :
    (∀ w : Vec 2, dot w (Example.initialMetric u A ρ ε *ᵥ w) =
        A * (w 0 - 2 * u * w 1) ^ 2 + (1 + ρ) * ε * (w 1) ^ 2) ∧
      (Example.initialMetric u A ρ ε).PosDef := by
  refine ⟨fun w => ?_, Example.initialMetric_posDef hA hρ hε⟩
  simp [dot, Example.initialMetric, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Item `C/10_Q/prose/045` (`companion/chapters/10_Q.tex:294`): "Thus these are strictly
Armijo--weak-Wolfe eligible unit steps." For $0<c_1<c_2<1$, $\rho$ as in display `disp/039`,
$\epsilon>0$, $\rho\epsilon<3u^2$ and $A>0$: $H_{\epsilon,\rho}$ is positive definite, the unit step
lands at $z_{\epsilon,\rho}$, Armijo and weak Wolfe hold strictly, and the pair is eligible. -/
theorem family_eligible (u A ε c₁ c₂ ρ : ℝ) (hA : 0 < A) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂)
    (hc₂ : c₂ < 1) (hρ : ρ = (1 - c₁) / (2 * c₁)) (hε : 0 < ε) (hs : ρ * ε < 3 * u ^ 2) :
    (Example.initialMetric u A ρ ε).PosDef ∧
      Example.oldPoint u ε + bfgsStep (Example.initialMetric u A ρ ε) (Example.oldGradient u) 1 =
        Example.newPoint u ρ ε ∧
      Example.objective (Example.newPoint u ρ ε) < Example.objective (Example.oldPoint u ε) +
        c₁ * dot (Example.oldGradient u)
          (bfgsStep (Example.initialMetric u A ρ ε) (Example.oldGradient u) 1) ∧
      c₂ * dot (Example.oldGradient u)
          (bfgsStep (Example.initialMetric u A ρ ε) (Example.oldGradient u) 1) <
        dot (Example.newGradient u)
          (bfgsStep (Example.initialMetric u A ρ ε) (Example.oldGradient u) 1) ∧
      EligiblePair Example.objective c₁ c₂ (Example.oldPoint u ε) (Example.newPoint u ρ ε)
        (Example.oldGradient u) (Example.newGradient u) := by
  obtain ⟨hρpos, hcρ, hlt⟩ := rho_choice c₁ c₂ hc₁ hc₁₂ hc₂ ρ hρ
  have hcρ' : c₁ * (1 + ρ) < 1 := by rw [hcρ]; exact hlt
  rw [Example.initialMetric_step u A ρ ε]
  have harm := Example.strict_armijo hρpos hε hs hcρ'
  have hdec : pairDecrease (Example.oldPoint u ε) (Example.newPoint u ρ ε)
      (Example.oldGradient u) = -dot (Example.oldGradient u)
        (pairStep (Example.oldPoint u ε) (Example.newPoint u ρ ε)) := rfl
  rw [hdec] at harm
  exact ⟨Example.initialMetric_posDef hA hρpos hε, by rw [pairStep]; abel, by linarith,
    Example.strict_weak_wolfe hρpos hε (by linarith),
    Example.pair_eligible hρpos hε hs hcρ'.le (by linarith)⟩

/-- Item `C/10_Q/prose/046` (`companion/chapters/10_Q.tex:300`): "In each neighborhood first fix a
sufficiently small nonzero $u$ and the resulting positive band; then the quotient exceeds any
proposed bound with arbitrarily small $d$." For every neighborhood $K$ of $0$, $0<c_1<c_2<1$, $\rho$
of display `disp/039` and $A>0$: some $u\ne0$ (fixed first; the pairs lie in the band $F\ge3u^2$)
such that for every $\delta>0$ and every bound $C$ some $\epsilon$ gives an eligible pair in $K$
with $F(z)=3u^2$, $d\le\delta$ and $C\,t<(y^Tz)^2$, together with its SPD unit-step metric
$H_{\epsilon,\rho}$. -/
theorem separation {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) (ρ : ℝ) (hρ : ρ = (1 - c₁) / (2 * c₁)) (A : ℝ) (hA : 0 < A) :
    ∃ u : ℝ, u ≠ 0 ∧ ∀ δ : ℝ, 0 < δ → ∀ C : ℝ, ∃ ε : ℝ, 0 < ε ∧ ρ * ε < 3 * u ^ 2 ∧
      Example.oldPoint u ε ∈ K ∧ Example.newPoint u ρ ε ∈ K ∧
      Example.objective (Example.newPoint u ρ ε) = 3 * u ^ 2 ∧
      EligiblePair Example.objective c₁ c₂ (Example.oldPoint u ε) (Example.newPoint u ρ ε)
        (Example.oldGradient u) (Example.newGradient u) ∧
      pairDecrease (Example.oldPoint u ε) (Example.newPoint u ρ ε) (Example.oldGradient u) ≤ δ ∧
      C * pairCurvature (Example.oldPoint u ε) (Example.newPoint u ρ ε) (Example.oldGradient u)
          (Example.newGradient u) <
        (RadialCertificate.radialNumerator 0 (Example.newPoint u ρ ε) (Example.oldGradient u)
          (Example.newGradient u)) ^ 2 ∧
      (Example.initialMetric u A ρ ε).PosDef ∧
      bfgsStep (Example.initialMetric u A ρ ε) (Example.oldGradient u) 1 =
        pairStep (Example.oldPoint u ε) (Example.newPoint u ρ ε) := by
  obtain ⟨hρpos, hcρ, hlt⟩ := rho_choice c₁ c₂ hc₁ hc₁₂ hc₂ ρ hρ
  obtain ⟨u, hu, hKu⟩ := Example.exists_nonzero_base_in_neighborhood hK
  refine ⟨u, hu, fun δ hδ C => ?_⟩
  obtain ⟨ε, hε, hs, hx, hz, hp, hd, he, hH, hstep⟩ :=
    Example.exists_small_eligible_excess_at_base (c₂ := c₂) hu hρpos
      (by rw [hcρ]; exact hlt.le) (by linarith) hA hKu hδ C
  exact ⟨ε, hε, hs, hx, hz, (Example.pair_values hρpos hε hs).2, hp, hd, he, hH, hstep⟩

/-- Item `C/10_Q/prose/047` (`companion/chapters/10_Q.tex:300`): "Hence the original (RS) condition
fails even on eligible near-stalling pairs for every fixed allowed line-search pair." For every
neighborhood $K$ of the minimizer and every $0<c_1<c_2<1$: (RS) on $K$
(`RadialCertificate.HasRadialSecantBounds`) fails, and on some positive band no constant $C$ and
threshold $\delta>0$ give $(y^Tz)^2\le C\,t$ even on the eligible pairs in $K$ with $d\le\delta$. -/
theorem rs_fails {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ¬ RadialCertificate.HasRadialSecantBounds Example.objective K 0 ∧
      ∃ η : ℝ, 0 < η ∧ ¬ ∃ C δ : ℝ, 0 < δ ∧ ∀ x z g g' : Vec 2, x ∈ K → z ∈ K →
        η ≤ Example.objective z → EligiblePair Example.objective c₁ c₂ x z g g' →
        pairDecrease x z g ≤ δ →
        (RadialCertificate.radialNumerator 0 z g g') ^ 2 ≤ C * pairCurvature x z g g' := by
  refine ⟨Example.not_radial_secant_on_neighborhood hK, ?_⟩
  obtain ⟨η, hη, h⟩ := Example.eligible_radial_unbounded_on_neighborhood hK
    (by linarith : c₁ < 1) (by linarith : 0 ≤ c₂)
  refine ⟨η, hη, fun ⟨C, δ, hδ, hb⟩ => ?_⟩
  obtain ⟨x, z, g, g', H, hx, hz, hηz, -, hp, hd, -, -, hC⟩ := h δ hδ C
  exact absurd (hb x z g g' hx hz hηz hp hd) (not_le.mpr hC)

/-- Item `C/10_Q/prose/049` (`companion/chapters/10_Q.tex:300`): "Every actual infinite admissible
run still converges by the main parabolic theorem." Every admissible run on the example converges,
although (RS) fails on every neighborhood of the minimizer (library
`converges_without_radial_secant`). -/
theorem converges_without_rs {K : Set (Vec 2)} (hK : K ∈ 𝓝 (0 : Vec 2)) :
    (∀ R : AdmissibleBFGSRun 2 Example.objective,
      Tendsto (fun k => Example.objective (R.x k)) atTop (𝓝 0) ∧ Tendsto R.x atTop (𝓝 0)) ∧
      ¬ RadialCertificate.HasRadialSecantBounds Example.objective K 0 :=
  Example.converges_without_radial_secant hK

/-- Item `C/10_Q/disp/043` (`companion/chapters/10_Q.tex:305-308`), with the claim of line 304: "In
contrast, $\theta(z_\epsilon)=1$ and
\[ y^Tr(z_\epsilon)=\epsilon,\qquad \frac{y^TW(z_\epsilon)y}{t}=\frac{2\epsilon}{3}\to0." \]
$W=(\theta r)(\theta r)^T$ with the printed scale (`example_field`), $y=g'-g$; for
$0<\epsilon<6u^2$, the limit as $\epsilon\downarrow0$ with $u\ne0$ fixed. -/
theorem printed_transported (u : ℝ) (hu : u ≠ 0) :
    (∀ ε, 0 < ε → ε < 6 * u ^ 2 → Example.sourceScale (Example.newPoint u (1 / 2) ε) = 1) ∧
      (∀ ε, dot (Example.newGradient u - Example.oldGradient u)
        (radialDirection (Example.newPoint u (1 / 2) ε)) = ε) ∧
      (∀ ε, 0 < ε → ε < 6 * u ^ 2 →
        dot (Example.newGradient u - Example.oldGradient u)
            (outer (Example.sourceVector (Example.newPoint u (1 / 2) ε))
              (Example.sourceVector (Example.newPoint u (1 / 2) ε)) *ᵥ
              (Example.newGradient u - Example.oldGradient u)) /
          pairCurvature (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)
            (Example.oldGradient u) (Example.newGradient u) = 2 * ε / 3) ∧
      Tendsto (fun ε => dot (Example.newGradient u - Example.oldGradient u)
            (outer (Example.sourceVector (Example.newPoint u (1 / 2) ε))
              (Example.sourceVector (Example.newPoint u (1 / 2) ε)) *ᵥ
              (Example.newGradient u - Example.oldGradient u)) /
          pairCurvature (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)
            (Example.oldGradient u) (Example.newGradient u)) (𝓝[>] 0) (𝓝 0) := by
  have hθ : ∀ ε, 0 < ε → ε < 6 * u ^ 2 → Example.sourceScale (Example.newPoint u (1 / 2) ε) = 1 :=
    fun ε hε hs => (Example.sourceScale_pair (by norm_num) hε (by linarith)).2
  have hnum : ∀ ε, dot (Example.newGradient u - Example.oldGradient u)
      (radialDirection (Example.newPoint u (1 / 2) ε)) = ε := fun ε => by
    rw [Example.transported_numerator]
    ring
  have hval : ∀ ε, 0 < ε → ε < 6 * u ^ 2 →
      dot (Example.newGradient u - Example.oldGradient u)
          (outer (Example.sourceVector (Example.newPoint u (1 / 2) ε))
            (Example.sourceVector (Example.newPoint u (1 / 2) ε)) *ᵥ
            (Example.newGradient u - Example.oldGradient u)) /
        pairCurvature (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)
          (Example.oldGradient u) (Example.newGradient u) = 2 * ε / 3 := by
    intro ε hε hs
    rw [rankOne_energy, Example.sourceVector, hθ ε hε hs, one_smul, hnum, Example.pair_curvature,
      div_eq_iff (mul_pos (by norm_num) hε).ne']
    ring
  refine ⟨hθ, hnum, hval, ?_⟩
  have hlim : Tendsto (fun ε : ℝ => 2 * ε / 3) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (h.const_mul 2).div_const 3
  apply hlim.congr'
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 6 * u ^ 2 :=
    (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds (mul_pos (by norm_num) (sq_pos_of_ne_zero hu)))
  filter_upwards [self_mem_nhdsWithin, hs] with ε hε hε'
  exact (hval ε hε hε').symm

/-- Item `C/10_Q/disp/044` (`companion/chapters/10_Q.tex:310-313`), with the claims of lines 309
and 314: "The unscaled quotient multiplier is $\lambda=1$, and the compensated multiplier satisfies
exactly
\[ \log\widetilde\lambda=\frac{\epsilon}{6(3u^2+\epsilon)}=O(d) \]
on each fixed positive band." For $0<\epsilon<6u^2$: $\lambda=1$; with the printed scale,
$\widetilde\lambda=\theta(z)\lambda/\theta(x)$ satisfies the identity and equals the library's
`compensatedMultiplier` (the normalization constant cancels); on the band $F\ge\eta$ ($\eta>0$,
containing $z_\epsilon$) the constant $1/(9\eta)$ gives $0\le\log\widetilde\lambda\le d/(9\eta)$. -/
theorem printed_multiplier (u ε : ℝ) (hε : 0 < ε) (hs : ε < 6 * u ^ 2) :
    quotientMultiplier (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) = 1 ∧
      Real.log (Example.sourceScale (Example.newPoint u (1 / 2) ε) *
          quotientMultiplier (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) /
          Example.sourceScale (Example.oldPoint u ε)) = ε / (6 * (3 * u ^ 2 + ε)) ∧
      Example.sourceScale (Example.newPoint u (1 / 2) ε) *
          quotientMultiplier (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) /
          Example.sourceScale (Example.oldPoint u ε) =
        Example.family.compensatedMultiplier (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε) ∧
      ∀ η : ℝ, 0 < η → η ≤ Example.objective (Example.newPoint u (1 / 2) ε) →
        0 ≤ ε / (6 * (3 * u ^ 2 + ε)) ∧
        ε / (6 * (3 * u ^ 2 + ε)) ≤
          1 / (9 * η) * pairDecrease (Example.oldPoint u ε) (Example.newPoint u (1 / 2) ε)
            (Example.oldGradient u) := by
  have hs' : 1 / 2 * ε < 3 * u ^ 2 := by linarith
  obtain ⟨hFx, hFz⟩ := Example.pair_values (by norm_num : (0 : ℝ) < 1 / 2) hε hs'
  have hpos : 0 < 3 * u ^ 2 + ε := add_pos_of_nonneg_of_pos (by positivity) hε
  refine ⟨Example.quotientMultiplier_eq_one u (1 / 2) ε,
    Example.source_compensated_log (by norm_num) hε hs', ?_, fun η hη hηz => ?_⟩
  · have hx : 0 < Example.objective (Example.oldPoint u ε) := by rw [hFx]; exact hpos
    have hz : 0 < Example.objective (Example.newPoint u (1 / 2) ε) := by rw [hFz]; linarith
    rw [Example.sourceScale_eq_normalized hx, Example.sourceScale_eq_normalized hz,
      Parabolic.Family.compensatedMultiplier, mul_assoc,
      mul_div_mul_left _ _ Example.sourceNormalization_pos.ne']
  · rw [hFz] at hηz
    refine ⟨div_nonneg hε.le (by positivity), ?_⟩
    rw [Example.pair_decrease]
    calc ε / (6 * (3 * u ^ 2 + ε)) ≤ ε / (6 * η) :=
          div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
      _ = 1 / (9 * η) * ((1 + 1 / 2) * ε) := by
          field_simp
          ring

/-- Item `C/10_Q/prose/054` (`companion/chapters/10_Q.tex:324`): "The theorem in this chapter
treats the complete stated finite family." In particular the special case $u^2+|v|$ (with $F$ a
variable with this defining equation) is the member $a=(1,1)$, $b=(1,-1)$, and the theorem gives
full convergence of every admissible run on it. -/
theorem mixed_in_family (F : Vec 2 → ℝ) (hF : ∀ x : Vec 2, F x = (x 0) ^ 2 + |x 1|) :
    (∀ x : Vec 2, IsGreatest (Set.range fun i => (![1, 1] : Fin 2 → ℝ) i * (x 0) ^ 2 +
      (![1, -1] : Fin 2 → ℝ) i * x 1) (F x)) ∧
      ∀ R : AdmissibleBFGSRun 2 F,
        Tendsto R.x atTop (𝓝 0) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 0) := by
  have hc : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  have hG : ∀ x : Vec 2, IsGreatest (Set.range fun i => (![1, 1] : Fin 2 → ℝ) i * (x 0) ^ 2 +
      (![1, -1] : Fin 2 → ℝ) i * x 1) (F x) := by
    intro x
    refine ⟨?_, ?_⟩
    · rcases le_or_lt 0 (x 1) with h | h
      · refine ⟨0, ?_⟩
        show 1 * (x 0) ^ 2 + 1 * x 1 = F x
        rw [hF, abs_of_nonneg h]
        ring
      · refine ⟨1, ?_⟩
        show 1 * (x 0) ^ 2 + -1 * x 1 = F x
        rw [hF, abs_of_neg h]
        ring
    · rintro _ ⟨i, rfl⟩
      have h1 := le_abs_self (x 1)
      have h2 := neg_abs_le (x 1)
      rcases hc i with rfl | rfl
      · show 1 * (x 0) ^ 2 + 1 * x 1 ≤ F x
        rw [hF]
        linarith
      · show 1 * (x 0) ^ 2 + -1 * x 1 ≤ F x
        rw [hF]
        linarith
  have ha : ∀ i, 0 < (![1, 1] : Fin 2 → ℝ) i := by
    intro i
    rcases hc i with rfl | rfl
    · show (0 : ℝ) < 1
      norm_num
    · show (0 : ℝ) < 1
      norm_num
  exact ⟨hG, fun R => parabolic_convergence _ _ ha ⟨1, by show (-1 : ℝ) < 0; norm_num⟩
    ⟨0, by show (0 : ℝ) < 1; norm_num⟩ F hG R⟩

/-! ### Non-vacuity -/

/-- The run on $u^2+|v|$ used below: the library's `UnexcitedMetric.run` with $A=1$, $v_0=1$,
$\rho=1/4$, $c_1=1/4$, $c_2=1/2$. -/
def absParabolaRun : AdmissibleBFGSRun 2 UnexcitedMetric.objective :=
  UnexcitedMetric.run 1 1 (1 / 4) (1 / 4) (1 / 2) one_pos one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The hypotheses of Theorem `theorem/001` (`parabolic_convergence`) and of `mixed_in_family` can
hold together with an admissible run: $F=u^2+|v|$, $a=(1,1)$, $b=(1,-1)$ and `absParabolaRun`. -/
example : ∃ (a b : Fin 2 → ℝ) (F : Vec 2 → ℝ), (∀ i, 0 < a i) ∧ (∃ i, b i < 0) ∧
    (∃ i, 0 < b i) ∧ (∀ x, IsGreatest (Set.range fun i => a i * (x 0) ^ 2 + b i * x 1) (F x)) ∧
    Nonempty (AdmissibleBFGSRun 2 F) := by
  have hc : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
  refine ⟨![1, 1], ![1, -1], UnexcitedMetric.objective, fun i => ?_,
    ⟨1, by show (-1 : ℝ) < 0; norm_num⟩, ⟨0, by show (0 : ℝ) < 1; norm_num⟩,
    (mixed_in_family _ fun _ => rfl).1, ⟨absParabolaRun⟩⟩
  rcases hc i with rfl | rfl
  · show (0 : ℝ) < 1
    norm_num
  · show (0 : ℝ) < 1
    norm_num

/-- Off the two switching parabolas the example objective is differentiable: exactly one branch
is active on a neighborhood. -/
theorem example_differentiableAt {x : Vec 2} (h1 : x 1 ≠ 2 * (x 0) ^ 2)
    (h2 : x 1 ≠ -(x 0) ^ 2) : DifferentiableAt ℝ Example.objective x := by
  rcases lt_or_gt_of_ne h1 with h1 | h1
  · rcases lt_or_gt_of_ne h2 with h2 | h2
    · have hc : Continuous (fun w : Vec 2 => -(w 0) ^ 2) := by fun_prop
      have he : Example.objective =ᶠ[𝓝 x] Example.family.branch 2 := by
        filter_upwards [(isOpen_lt (continuous_apply 1) hc).mem_nhds h2] with w hw
        exact (example_switching.2.2.1 w).mpr hw.le
      exact (Example.family.branch_hasGradient 2 x).differentiableAt.congr_of_eventuallyEq he
    · exact (Example.middle_hasGradient h2 h1).differentiableAt
  · exact (Example.upper_hasGradient h1).differentiableAt

/-- Every line $x+tp$ ($p\ne0$) meets the switching parabolas $v=2u^2$, $v=-u^2$ in finitely many
points (along the line each is a quadratic equation in $t$ whose coefficients do not all vanish),
so the example objective is differentiable at all but finitely many points of the line. -/
theorem example_line_finite (x p : Vec 2) (hp : p ≠ 0) :
    {t : ℝ | ¬ DifferentiableAt ℝ Example.objective (x + t • p)}.Finite := by
  have hp2 : 0 < p 0 ^ 2 + p 1 ^ 2 := by
    by_contra hle
    apply hp
    have h0 : p 0 ^ 2 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have h1 : p 1 ^ 2 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hA : {t : ℝ | (x + t • p) 1 = 2 * ((x + t • p) 0) ^ 2}.Finite := by
    refine (AdmissibleRunExistence.quadratic_zeros_finite
      (a := 2 * p 0 ^ 2) (b := 4 * x 0 * p 0 - p 1) (c := 2 * x 0 ^ 2 - x 1) ?_).subset ?_
    · rintro ⟨ha, hb, -⟩
      have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0)]
      have h1 : p 1 = 0 := by rw [h0] at hb; linarith
      rw [h0, h1] at hp2
      norm_num at hp2
    · intro t ht
      simp only [mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht ⊢
      linear_combination (-1 : ℝ) * ht
  have hB : {t : ℝ | (x + t • p) 1 = -((x + t • p) 0) ^ 2}.Finite := by
    refine (AdmissibleRunExistence.quadratic_zeros_finite
      (a := p 0 ^ 2) (b := 2 * x 0 * p 0 + p 1) (c := x 0 ^ 2 + x 1) ?_).subset ?_
    · rintro ⟨ha, hb, -⟩
      have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0)]
      have h1 : p 1 = 0 := by rw [h0] at hb; linarith
      rw [h0, h1] at hp2
      norm_num at hp2
    · intro t ht
      simp only [mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht ⊢
      linear_combination ht
  refine (hA.union hB).subset fun t ht => ?_
  by_contra hn
  simp only [mem_union, mem_setOf_eq, not_or] at hn
  exact ht (example_differentiableAt hn.1 hn.2)

/-- No point of differentiability of the example objective has gradient zero: such a point would
be the minimizer $0$, where $F\ge u^2+v$ with equality would force the gradient $(0,1)$. -/
theorem example_gradient_ne_zero {y g : Vec 2}
    (h : HasFDerivAt Example.objective (gradientFunctional g) y) : g ≠ 0 := by
  rintro rfl
  have hconv : ConvexOn ℝ univ Example.objective := Example.family.objective_convex
  have hF0 : Example.objective 0 = 0 := Example.family.objective_zero
  have hmin : ∀ z, Example.objective y ≤ Example.objective z := by
    intro z
    have hs := convex_supporting_inequality hconv h z
    simp [dot] at hs
    linarith
  have hy0 : Example.objective y = 0 :=
    le_antisymm ((hmin 0).trans_eq hF0) (Example.family.objective_nonneg y)
  have hy : y = 0 := Example.family.unique_zero y hy0
  subst hy
  have h00 : Example.family.branch 0 0 = 0 := by simp [Parabolic.Family.branch]
  have hloc : IsLocalMin (fun z => Example.objective z - Example.family.branch 0 z) 0 := by
    refine Filter.Eventually.of_forall fun z => ?_
    have hz : Example.family.branch 0 z ≤ Example.objective z := Example.family.branch_le 0 z
    show Example.objective 0 - Example.family.branch 0 0 ≤
      Example.objective z - Example.family.branch 0 z
    rw [hF0, h00]
    linarith
  have h0 := hloc.hasFDerivAt_eq_zero (h.sub (Example.family.branch_hasGradient 0 0))
  have he := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L ![0, 1]) h0
  simp [Parabolic.Family.branchGradient, Example.family, dot, Fin.sum_univ_two] at he

/-- Admissible runs on the example objective (10.18) exist from every point of
differentiability, for every $H_0\succ0$ and all $0<c_1<c_2<1$
(`AdmissibleRunExistence.exists_admissible_run`: the objective is convex, bounded below,
differentiable at all but finitely many points of every line, and has no zero gradient). -/
theorem example_run_exists {x₀ g₀ : Vec 2}
    (hg₀ : HasFDerivAt Example.objective (gradientFunctional g₀) x₀) {H₀ : Mat 2}
    (hH₀ : H₀.PosDef) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ R : AdmissibleBFGSRun 2 Example.objective,
      R.x 0 = x₀ ∧ R.g 0 = g₀ ∧ R.H 0 = H₀ ∧ R.c₁ = c₁ ∧ R.c₂ = c₂ := by
  have hconv : ConvexOn ℝ univ Example.objective := Example.family.objective_convex
  exact AdmissibleRunExistence.exists_admissible_run hconv
    ⟨0, by rintro _ ⟨x, rfl⟩; exact Example.family.objective_nonneg x⟩
    (fun x p _ hp => (example_line_finite x p hp).countable)
    (fun _ _ h => example_gradient_ne_zero h) hg₀ hH₀ hc₁ hc₁₂ hc₂

/-- An admissible run on the example objective: from $x_0=(1,3)$ (only $u^2+v$ active, gradient
$(2,1)$), $H_0=I$, $c_1=1/4$, $c_2=1/2$. -/
theorem exampleRun_nonempty : Nonempty (AdmissibleBFGSRun 2 Example.objective) := by
  obtain ⟨R, -⟩ := example_run_exists
    (Example.upper_hasGradient (x := Example.oldPoint 1 1) (by norm_num [Example.oldPoint]))
    Matrix.PosDef.one (c₁ := 1 / 4) (c₂ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨R⟩

/-- The "every run" conclusion of `example_flat_contour` (item `prose/001`) is not vacuous:
admissible runs on the example objective exist (`example_run_exists`). -/
example : ∃ R : AdmissibleBFGSRun 2 Example.objective, Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨R⟩ := exampleRun_nonempty
  exact ⟨R, (example_flat_contour.2.2 R).2⟩

/-- The conclusion of `example_applies` (item `prose/031`) is not vacuous: it applies to the runs
of `example_run_exists`. -/
example : ∃ R : AdmissibleBFGSRun 2 Example.objective,
    Tendsto (fun k => Example.objective (R.x k)) atTop (𝓝 0) := by
  obtain ⟨R⟩ := exampleRun_nonempty
  exact ⟨R, (example_applies.2.2.2 R).2⟩

/-- The convergence conclusion of `converges_without_rs` (item `prose/049`) is not vacuous: it
applies to the runs of `example_run_exists` (here with $K=\R^2$). -/
example : ∃ R : AdmissibleBFGSRun 2 Example.objective, Tendsto R.x atTop (𝓝 0) := by
  obtain ⟨R⟩ := exampleRun_nonempty
  exact ⟨R, ((converges_without_rs (K := univ) Filter.univ_mem).1 R).2⟩

/-- All three branches of the example family are essential. -/
theorem example_essential (i : Fin 3) : Example.family.Essential i := by
  have hc : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have ha0 : Example.family.a 0 = 1 := rfl
  have ha1 : Example.family.a 1 = 3 := rfl
  have ha2 : Example.family.a 2 = 2 := rfl
  have hb0 : Example.family.b 0 = 1 := rfl
  have hb1 : Example.family.b 1 = 0 := rfl
  have hb2 : Example.family.b 2 = -1 := rfl
  have hcan : ∀ i : Fin 3, Example.family.Canonical i := by
    intro i j ha _
    rcases hc i with rfl | rfl | rfl <;> rcases hc j with rfl | rfl | rfl
    all_goals first
      | decide
      | (norm_num [ha0, ha1, ha2] at ha)
  refine ⟨hcan i, ?_⟩
  rcases hc i with rfl | rfl | rfl
  · refine ⟨3, fun j _ hj => ?_⟩
    rcases hc j with rfl | rfl | rfl
    · exact absurd rfl hj
    · norm_num [Parabolic.Family.profile, ha0, ha1, hb0, hb1]
    · norm_num [Parabolic.Family.profile, ha0, ha2, hb0, hb2]
  · refine ⟨0, fun j _ hj => ?_⟩
    rcases hc j with rfl | rfl | rfl
    · norm_num [Parabolic.Family.profile, ha0, ha1, hb0, hb1]
    · exact absurd rfl hj
    · norm_num [Parabolic.Family.profile, ha1, ha2, hb1, hb2]
  · refine ⟨-2, fun j _ hj => ?_⟩
    rcases hc j with rfl | rfl | rfl
    · norm_num [Parabolic.Family.profile, ha0, ha2, hb0, hb2]
    · norm_num [Parabolic.Family.profile, ha1, ha2, hb1, hb2]
    · exact absurd rfl hj

/-- An explicit ordered pruned list of the example family: the branches $2u^2-v$, $3u^2$, $u^2+v$
(slopes $-1<0<1$). -/
def examplePrunedOrder : Example.family.PrunedOrder where
  count := 3
  count_pos := by norm_num
  index := ![2, 1, 0]
  essential _ := example_essential _
  covers i _ := by
    have hc : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hc i with rfl | rfl | rfl
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  slopes_strictMono := by
    have hb0 : Example.family.b 0 = 1 := rfl
    have hb1 : Example.family.b 1 = 0 := rfl
    have hb2 : Example.family.b 2 = -1 := rfl
    have h21 : Example.family.b 2 < Example.family.b 1 := by rw [hb2, hb1]; norm_num
    have h20 : Example.family.b 2 < Example.family.b 0 := by rw [hb2, hb0]; norm_num
    have h10 : Example.family.b 1 < Example.family.b 0 := by rw [hb1, hb0]; norm_num
    intro i j hij
    have hc : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
    rcases hc i with rfl | rfl | rfl <;> rcases hc j with rfl | rfl | rfl
    all_goals first
      | exact absurd hij (by decide)
      | exact h21
      | exact h20
      | exact h10

/-- The standing assumptions of the statements on consecutive pieces of an ordered pruned list
(`breakpoints_increasing` with three consecutive pieces, `breakpoint_value`,
`calibration_recursion`, `tie_difference`) can hold: `examplePrunedOrder` has three pieces. -/
example : ∃ (O : Example.family.PrunedOrder) (i j k : Fin O.count),
    j.val = i.val + 1 ∧ k.val = j.val + 1 :=
  ⟨examplePrunedOrder, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, rfl, rfl⟩

/-- The standing assumptions of the band statements (`deficits_nonneg` to `transport_loewner`) can
hold, with arbitrarily small decrease: for the example family, $x=(1,2+\epsilon)$ and
$z=(1,2-\epsilon)$ ($\rho=1$, $0<\epsilon\le1/2$) lie in the band $3\le F\le4$, the branches $u^2+v$
and $3u^2$ are active there, and the pair is eligible for $c_1=1/4$, $c_2=1/2$ with $d=2\epsilon$.
-/
example : ∀ δ : ℝ, 0 < δ → ∃ x z g g' : Vec 2,
    (3 ≤ Example.family.objective x ∧ Example.family.objective x ≤ 4) ∧
    (3 ≤ Example.family.objective z ∧ Example.family.objective z ≤ 4) ∧
    Example.family.Active 0 x ∧ Example.family.Active 1 z ∧
    HasFDerivAt Example.family.objective (gradientFunctional g) x ∧
    HasFDerivAt Example.family.objective (gradientFunctional g') z ∧
    EligiblePair Example.family.objective (1 / 4) (1 / 2) x z g g' ∧ pairDecrease x z g ≤ δ := by
  intro δ hδ
  obtain ⟨hA0, hA1, -, -⟩ := example_switching
  set ε := min (1 / 2) (δ / 2) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ δ / 2 := min_le_right _ _
  have hs : 1 * ε < 3 * 1 ^ 2 := by linarith
  obtain ⟨hFx, hFz⟩ := Example.pair_values (by norm_num : (0 : ℝ) < 1) hε0 hs
  obtain ⟨hg, hg'⟩ := Example.pair_gradients (by norm_num : (0 : ℝ) < 1) hε0 hs
  have hFx' : Example.family.objective (Example.oldPoint 1 ε) = 3 + ε := by
    rw [show Example.family.objective = Example.objective from rfl, hFx]
    ring
  have hFz' : Example.family.objective (Example.newPoint 1 1 ε) = 3 := by
    rw [show Example.family.objective = Example.objective from rfl, hFz]
    ring
  refine ⟨Example.oldPoint 1 ε, Example.newPoint 1 1 ε, Example.oldGradient 1,
    Example.newGradient 1, ⟨by rw [hFx']; linarith, by rw [hFx']; linarith⟩,
    ⟨by rw [hFz'], by rw [hFz']; norm_num⟩, (hA0 _).mpr ?_, (hA1 _).mpr ⟨?_, ?_⟩, hg, hg',
    Example.pair_eligible (by norm_num) hε0 hs (by norm_num) (by norm_num), ?_⟩
  · show 2 * (1 : ℝ) ^ 2 ≤ 2 * 1 ^ 2 + ε
    linarith
  · show -(1 : ℝ) ^ 2 ≤ 2 * 1 ^ 2 - 1 * ε
    linarith
  · show 2 * (1 : ℝ) ^ 2 - 1 * ε ≤ 2 * 1 ^ 2
    linarith
  · rw [Example.pair_decrease]
    linarith

/-- The standing assumptions of the example's pair statements can hold: $u=A=\epsilon=1$
($0<\epsilon<6u^2$), $c_1=1/4\le2/3$, $c_2=1/2$; then $\alpha=1$ is an accepted unit step
(`printed_acceptance`). -/
example : ∃ u A ε c₁ c₂ : ℝ, u ≠ 0 ∧ 0 < A ∧ 0 < ε ∧ ε < 6 * u ^ 2 ∧ 0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧
    c₁ ≤ 2 / 3 :=
  ⟨1, 1, 1, 1 / 4, 1 / 2, one_ne_zero, one_pos, one_pos, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

end BfgsCoverage.Companion.Ch10Q
