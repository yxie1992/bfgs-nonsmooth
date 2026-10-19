import BfgsVerification.PlanarAllEndpoints
import BfgsVerification.PlanarQuadraticConvergence

/-!
# Lean coverage: `paper/appendices/planar_geometry.tex`

Appendix `art:planar-appendix` ("Constructing the planar comparison field"): Lemma
`art:planar-field` ("One field with all endpoint estimates") and its proof. Register:
`editorial/lean_coverage/register/A_planar_geometry.json`.

## Standing assumptions

Every theorem below states the hypotheses of Lemma `art:planar-field`
(`paper/appendices/planar_geometry.tex:7-16`) explicitly, with these names:

* `F : Vec 2 → ℝ` and `hF : ConvexOn ℝ univ F`: $F:\R^2\to\R$ finite and convex;
* `Fstar` and `hFstar : IsLeast (range F) Fstar`: $F$ attains its minimum $F_*$;
* `C`, `ℓ`, `hCne : C.Nonempty`, `hCcpt : IsCompact C`, `hCℓ : C ⊆ {x | F x = ℓ}`,
  `hℓ : Fstar < ℓ`: $C\subset\{F=\ell\}$ is nonempty and compact, $\ell>F_*$;
* `hstrict : ∀ x y, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y`: the boundary of
  $\{F\le\ell\}$ contains no nontrivial segment;
* `hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p`: no point of $C$ is affine critical, where
  `IsAffineCritical F p` is $0\in\aff\partial F(p)$ (`local.tex:153-156`);
* `hregular`: every `p ∈ C` has the smooth or regular convex two-branch structure of
  hypothesis 2 of Theorem `art:planar-cluster` (`local.tex:218-221`), written as in the TeX (and
  as in the coverage of `local.tex`): either $F$ is $C^2$ on an open `V ∋ p`, or on an open
  `V ∋ p`, $F=\max\{f_1,f_2\}$ with $f_1,f_2$ convex and $C^2$ on `V` (so `V` is convex), both
  active at $p$, and $\nabla f_1(p),\nabla f_2(p)$ linearly independent. `regularity_of_literal`
  and `literal_of_regularity` show that this is the library's
  `ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p`. The corner theorems below write the
  two-branch data at a corner as variables (`V`, `f₁`, `f₂`, `hf₁`, ..., `hind`);
* `c₁ c₂` with `0 < c₁`, `c₁ < c₂`, `c₂ < 1`: valid Armijo--weak-Wolfe constants.

A hypothesis whose name starts with `_` is one of these assumptions (or of the objects below)
that the Lean proof does not need. Each display of the proof is stated under these
assumptions and the objects and facts that the proof has introduced before it, written as
variables with their defining equations or properties.

## Notation

* `Vec 2 = Fin 2 → ℝ` carries the sup norm; Euclidean quantities are explicit:
  `‖euclideanVector s‖` is $\norm{s}$, `sqNorm s` is $\norm{s}^2$, `dot a b` is $a^Tb$.
* `pairDet a b = a 0 * b 1 - a 1 * b 0` is $\det(a,b)$, the determinant with columns $a,b$.
* `normal θ = ![cos θ, sin θ]` is $n(\theta)$, `tangent θ = ![-sin θ, cos θ]` is $T(\theta)$;
  `PlanarAmbientFrame.rotate u = ![-u 1, u 0]`, so `rotate (normal θ) = tangent θ`.
* `normalized g = ‖euclideanVector g‖⁻¹ • g` is $g/\norm{g}$; `coordinateGradient F x` is
  $\nabla F(x)$; `subdifferential F x` is $\partial F(x)$.
* For differentiable $x,z$ (energy.tex:234-239), `EligiblePair F c₁ c₂ x z g h` says that
  `g`, `h` are the gradients at `x`, `z` and that the pair is eligible:
  $d>0$, $c_1d\le\Delta\le d$, $t\ge(1-c_2)d$, with $s=z-x$, $y=h-g$, $d=-g^Ts$
  (`-dot g (z - x)`), $\Delta=F(x)-F(z)$ and $t=y^Ts$ (`dot (h - g) (z - x)`).
* The angular cutoffs of the proof are `fun j θ => χ j (normal θ)` for smooth ambient
  cutoffs `χ : Fin m → Vec 2 → ℝ` (so they are smooth and $2\pi$-periodic in θ), and the
  velocities are `v : Fin m → ℝ → Vec 2`. `height χ v t θ` is $h(t,\theta)$
  (`art:planar-height`) and `fieldFormula χ v t θ` is $hn+h_\theta T$ at $(t,\theta)$
  (`art:planar-field-formula`). The field constructed in the proof is the library's
  `PlanarObjectiveField.field hF χ v`; `field_eq_fieldFormula` shows that it is given by
  (`art:planar-field-formula`) at every smooth point and every angle of its normal, and
  `corner_field` that it equals $v_j(F(x))$ near the $j$th corner (`art:planar-corner-field`).

## Items

| Item | Lines | Lean |
|---|---|---|
| `lemma/art:planar-field` (with `disp/001`, `disp/002`) | 8-38 | `planar_field` |
| `disp/003` (`art:corner-velocity`) | 46-49 | `corner_velocity` |
| `disp/004` (`art:planar-height`) | 73-76 | `height`, `height_eq_library` |
| `disp/005` (`art:planar-field-formula`) | 85-88 | `fieldFormula`, `field_eq_fieldFormula` |
| `disp/006` (`art:planar-corner-field`) | 92-94 | `corner_field_formula`, `corner_field` |
| `disp/007` | 100-102 | `smooth_pairing` |
| `disp/008` (`art:planar-tangent-cancellation`) | 112-114 | `tangent_cancellation` |
| `disp/009` | 117-119 | `derivative_triangular`, `derivative_coefficients_bounded` |
| `disp/010` | 136-139 | `transversality_limits` |
| `disp/011` (`art:planar-determinant-derivative`) | 150-152 | `determinant_derivative` |
| `disp/012` | 160-164 | `log_determinant_derivative_bound` |
| `disp/013` | 175-178 | `comparison_functions` |
| `disp/014` | 181-183 | `log_determinant_increment` |
| `disp/015` | 196-199 | `branch_cocoercivity` |
| `disp/016` | 214-216 | `crossing_numerator` |
| `disp/017` | 219-221 | `crossing_pairings` |
| `disp/018` | 224-227 | `crossing_step_bound` |

Undisplayed steps of the proof that are stated as well: `corner_curve` (lines 41-44),
`exists_angle` and `fieldFormula_periodic` (line 89), `transversality_contradiction`
(lines 140-141), `one_sided_comparison` (lines 170-175), `transport_constants` (lines 186-191),
`same_branch_secant` (lines 208-210), `crossing_tie_point` (lines 212-214) and
`crossing_secant` (lines 230-232). `planar_field` itself is proved from the library theorem
`PlanarAllPairs.source_all_endpoint_estimates`, which follows the same construction.

The `example`s at the end show that the hypotheses of every theorem above hold together for the
objective of Theorem `art:nonradial-example`, with $C=\{p_0\}$ for a point $p_0$ where two
branches tie: the standing assumptions, the corner data with the curve and field of the proof
(`corner_curve`, `corner_velocity`, `corner_field`), a smooth point and an eligible pair
(`derivative_triangular`, `determinant_derivative`, `smooth_pairing`, `corner_field_formula`,
`tangent_cancellation`, the transport theorems, `branch_cocoercivity`, `same_branch_secant`),
the library construction (`log_determinant_derivative_bound`,
`derivative_coefficients_bounded`), an eligible pair crossing the switching curve (the five
crossing theorems) and the eligibility-free case of `transversality_limits`. The exception is
`transversality_contradiction`, whose assumptions are contradictory by design.
-/

noncomputable section
open scoped Topology NNReal ContDiff
open Set Filter BfgsVerification
open BfgsVerification.ConvexSubdifferential BfgsVerification.TransportedCertificate
  BfgsVerification.HomogeneousPlanar BfgsVerification.PlanarTransport
  BfgsVerification.PlanarCornerCharts BfgsVerification.AffineCriticalObjective
  BfgsVerification.PlanarNormalGeometry

namespace BfgsCoverage.Article.PlanarGeometry

/-! ### Definitions -/

/-- Item `A/planar_geometry/disp/004` (`paper/appendices/planar_geometry.tex:71-74`), equation
`art:planar-height`, in the proof of Lemma `art:planar-field`: the definition
\[ h(t,\theta)=1+\sum_j\chi_j(\theta)\bigl(n(\theta)^Tv_j(t)-1\bigr) \]
for angular cutoffs $\chi_j$ and velocities $v_j$. -/
def height {m : ℕ} (χ : Fin m → ℝ → ℝ) (v : Fin m → ℝ → Vec 2) (t θ : ℝ) : ℝ :=
  1 + ∑ j, χ j θ * (dot (normal θ) (v j t) - 1)

/-- Item `A/planar_geometry/disp/005` (`paper/appendices/planar_geometry.tex:83-86`), equation
`art:planar-field-formula`, in the proof of Lemma `art:planar-field`: the right side of
\[ w(x)=h(F(x),\theta(x))n(\theta(x))+h_\theta(F(x),\theta(x))T(\theta(x)), \]
as a function of $t=F(x)$ and of the normal angle $\theta=\theta(x)$, with
$h_\theta=\partial_\theta h$. -/
def fieldFormula {m : ℕ} (χ : Fin m → ℝ → ℝ) (v : Fin m → ℝ → Vec 2) (t θ : ℝ) : Vec 2 :=
  height χ v t θ • normal θ + deriv (height χ v t) θ • tangent θ

/-- Two vectors of the plane are linearly independent only if their determinant is nonzero. -/
theorem pairDet_ne_zero_of_independent {a b : Vec 2} (h : LinearIndependent ℝ ![a, b]) :
    pairDet a b ≠ 0 := by
  rw [LinearIndependent.pair_iff] at h
  intro hd
  simp only [pairDet] at hd
  have h1 := h (b 1) (-a 1) (by ext i; fin_cases i <;> simp <;> linarith)
  have h2 := h (b 0) (-a 0) (by ext i; fin_cases i <;> simp <;> linarith)
  have ha : a = 0 := by
    ext i
    fin_cases i
    · simpa using h2.2
    · simpa using h1.2
  have h3 := h 1 0 (by simp [ha])
  exact one_ne_zero h3.1

/-- Two vectors of the plane with nonzero determinant are linearly independent. -/
theorem independent_of_pairDet_ne_zero {a b : Vec 2} (h : pairDet a b ≠ 0) :
    LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  simp only [pairDet] at h
  constructor
  · have : s * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination b 1 * h0 - b 0 * h1
    exact (mul_eq_zero.mp this).resolve_right h
  · have : t * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination a 0 * h1 - a 1 * h0
    exact (mul_eq_zero.mp this).resolve_right h

/-- $F(z)=\max\{f_0(z),f_1(z)\}$ in the library's form of a finite maximum. -/
theorem isGreatest_of_max {F : Vec 2 → ℝ} (f : Fin 2 → Vec 2 → ℝ) {z : Vec 2}
    (h : F z = max (f 0 z) (f 1 z)) : IsGreatest (range fun i => f i z) (F z) := by
  rw [h]
  refine ⟨?_, ?_⟩
  · rcases max_choice (f 0 z) (f 1 z) with hm | hm
    · exact ⟨0, hm.symm⟩
    · exact ⟨1, hm.symm⟩
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- The library's form of a finite maximum of two branches is $F=\max\{f_0,f_1\}$. -/
theorem max_of_isGreatest {F : Vec 2 → ℝ} (f : Fin 2 → Vec 2 → ℝ) {z : Vec 2}
    (h : IsGreatest (range fun i => f i z) (F z)) : F z = max (f 0 z) (f 1 z) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := h.1
    rw [← hi]
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (h.2 ⟨0, rfl⟩) (h.2 ⟨1, rfl⟩)

/-- `ContDiffAt ℝ 2 F p` says that $F$ is $C^2$ in a neighborhood of $p$. -/
theorem contDiffAt_two_iff (F : Vec 2 → ℝ) (p : Vec 2) :
    ContDiffAt ℝ 2 F p ↔ ∃ N ∈ 𝓝 p, ContDiffOn ℝ 2 F N :=
  ⟨fun h => h.contDiffOn le_rfl (by simp), fun ⟨_, hN, hC⟩ => hC.contDiffAt hN⟩

/-- Notation (`hregular`): the smooth or regular convex two-branch structure of hypothesis 2 of
Theorem `art:planar-cluster` (`local.tex:218-221`), written as in the TeX (the form of `hregular`
in this file), implies the library's form `ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p`
used by `PlanarAllPairs.source_all_endpoint_estimates`. -/
theorem regularity_of_literal {F : Vec 2 → ℝ} {p : Vec 2}
    (h : (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) :
    ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p := by
  rcases h with ⟨V, hV, hpV, hC⟩ | ⟨V, hV, hpV, f₁, f₂, hc₁, hc₂, hC₁, hC₂, hmax, h₁, h₂, hind⟩
  · exact Or.inl (hC.contDiffAt (hV.mem_nhds hpV))
  · right
    refine ⟨![f₁, f₂], V, hV, hpV, ?_, fun z hz => isGreatest_of_max ![f₁, f₂] (hmax z hz), ?_,
      pairDet_ne_zero_of_independent hind⟩
    · intro i
      fin_cases i
      · exact ⟨hc₁, hC₁⟩
      · exact ⟨hc₂, hC₂⟩
    · intro i
      fin_cases i
      · exact h₁
      · exact h₂

/-- Notation (`hregular`): conversely, the library's form implies the TeX form, so the two
readings of hypothesis 2 of Theorem `art:planar-cluster` agree. -/
theorem literal_of_regularity {F : Vec 2 → ℝ} {p : Vec 2}
    (h : ContDiffAt ℝ 2 F p ∨ ConvexTwoBranchRegularAt F p) :
    (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]) := by
  rcases h with hC | ⟨f, U, hU, hpU, hf, hrep, hact, hdet⟩
  · obtain ⟨N, hN, hCN⟩ := (contDiffAt_two_iff F p).mp hC
    exact Or.inl ⟨interior N, isOpen_interior, mem_interior_iff_mem_nhds.mpr hN,
      hCN.mono interior_subset⟩
  · exact Or.inr ⟨U, hU, hpU, f 0, f 1, (hf 0).1, (hf 1).1, (hf 0).2, (hf 1).2,
      fun z hz => max_of_isGreatest f (hrep z hz), hact 0, hact 1,
      independent_of_pairDet_ne_zero hdet⟩

/-- Notation (`hnoncrit`): `IsAffineCritical F p` is $0\in\aff\partial F(p)$ (`local.tex:153-156`),
the affine span taken in Euclidean space. -/
theorem isAffineCritical_iff (F : Vec 2 → ℝ) (p : Vec 2) :
    IsAffineCritical F p ↔
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ affineSpan ℝ (euclideanVector '' subdifferential F p) := by
  rw [IsAffineCritical, range_subgradientFamily]

/-- Unfolding theorem for `height` (`art:planar-height`): with the angular cutoffs
$\chi_j(\theta)=\chi_j(n(\theta))$ of smooth ambient cutoffs, `height` is the library's angular
height `PlanarJoinedFrame.height` and its ambient form `PlanarAmbientFrame.height` at the unit
normal $n(\theta)$, both used to build the field of the library proof. -/
theorem height_eq_library {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2)
    (t θ : ℝ) :
    height (fun j φ => χ j (normal φ)) v t θ = PlanarJoinedFrame.height χ (fun j => v j t) θ ∧
      height (fun j φ => χ j (normal φ)) v t θ =
        PlanarAmbientFrame.height χ (fun j => v j t) (normal θ) := ⟨rfl, rfl⟩

/-- Unfolding theorem for `fieldFormula` (`art:planar-field-formula`): at a point $x$ where
$F$ has gradient $g$ ("smooth point"), for every angle $\theta$ with
$n(\theta)=g/\norm{g}$, the library's field `PlanarObjectiveField.field hF χ v` (the field of
the proof, built from smooth ambient cutoffs `χ`) is
$h(F(x),\theta)n(\theta)+h_\theta(F(x),\theta)T(\theta)$ with the angular cutoffs
$\theta\mapsto\chi_j(n(\theta))$. -/
theorem field_eq_fieldFormula {m : ℕ} {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, Differentiable ℝ (χ j)) (v : Fin m → ℝ → Vec 2)
    {x g : Vec 2} (hg : HasFDerivAt F (gradientFunctional g) x)
    (θ : ℝ) (hθ : normal θ = normalized g) :
    PlanarObjectiveField.field hF χ v x = fieldFormula (fun j φ => χ j (normal φ)) v (F x) θ := by
  rw [PlanarObjectiveField.field_eq_gradient_formula hF χ v hg, ← hθ,
    PlanarAmbientFrame.frame_eq_angular_frame _ hχ θ]
  rfl

/-- Proof of Lemma `art:planar-field`, the angle in `paper/appendices/planar_geometry.tex:82`
(not a register item): every Euclidean unit vector is a normal $n(\theta)$, so
$\theta(x)$ with $n(\theta(x))=\nabla F(x)/\norm{\nabla F(x)}$ exists at every point with
nonzero gradient. -/
theorem exists_angle (u : Vec 2) (hu : sqNorm u = 1) : ∃ θ : ℝ, normal θ = u := by
  let z : ℂ := ⟨u 0, u 1⟩
  have hz : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [sqNorm, Fin.sum_univ_two] at hu
      simp [z]
      nlinarith
    have h2 : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  refine ⟨Complex.arg z, ?_⟩
  ext i
  fin_cases i
  · simp [normal, Complex.cos_arg hz0, hz, z]
  · simp [normal, Complex.sin_arg, hz, z]

/-- Proof of Lemma `art:planar-field`, undisplayed claim of
`paper/appendices/planar_geometry.tex:87` (not a register item): "All expressions are
periodic, so no global choice of angle is required." For angular cutoffs
$\theta\mapsto\chi_j(n(\theta))$, the formula (`art:planar-field-formula`) is
$2\pi$-periodic in $\theta$. -/
theorem fieldFormula_periodic {m : ℕ} (χ : Fin m → Vec 2 → ℝ) (v : Fin m → ℝ → Vec 2)
    (t θ : ℝ) :
    fieldFormula (fun j φ => χ j (normal φ)) v t (θ + 2 * Real.pi) =
      fieldFormula (fun j φ => χ j (normal φ)) v t θ :=
  PlanarJoinedFrame.frame_periodic χ (fun j => v j t) θ

/-! ### Helpers -/

/-- $a^T(-b)=-a^Tb$. -/
theorem dot_neg_right_vec (a b : Vec 2) : dot a (-b) = -dot a b := by
  simp [dot]

/-- $a^T(s/\norm{s})=a^Ts/\norm{s}$. -/
theorem dot_normalized_right (a s : Vec 2) :
    dot a (normalized s) = dot a s / ‖euclideanVector s‖ := by
  rw [normalized, dot_smul_right, div_eq_inv_mul]

/-- The Euclidean realization is linear: scalars. -/
theorem euclideanVector_smul (τ : ℝ) (u : Vec 2) :
    euclideanVector (τ • u) = τ • euclideanVector u := rfl

/-- The Euclidean realization is linear: differences. -/
theorem euclideanVector_sub (a b : Vec 2) :
    euclideanVector (a - b) = euclideanVector a - euclideanVector b := rfl

/-- $\norm{u}^2$ is `sqNorm u`. -/
theorem euclidean_norm_sq_eq (u : Vec 2) : ‖euclideanVector u‖ ^ 2 = sqNorm u :=
  FrameNorms.euclidean_norm_sq (euclideanVector u)

/-- A point of the segment $[x,z]$ is within $\norm{z-x}$ of both endpoints. -/
theorem segment_euclidean_dist {x z p : Vec 2} (hp : p ∈ segment ℝ x z) :
    ‖euclideanVector (p - x)‖ ≤ ‖euclideanVector (z - x)‖ ∧
      ‖euclideanVector (z - p)‖ ≤ ‖euclideanVector (z - x)‖ := by
  rw [segment_eq_image'] at hp
  obtain ⟨τ, hτ, rfl⟩ := hp
  have h1 : x + τ • (z - x) - x = τ • (z - x) := by abel
  have h2 : z - (x + τ • (z - x)) = (1 - τ) • (z - x) := by module
  rw [h1, h2, euclideanVector_smul, euclideanVector_smul, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hτ.1, abs_of_nonneg (sub_nonneg.mpr hτ.2)]
  have hn := norm_nonneg (euclideanVector (z - x))
  constructor <;> nlinarith [hτ.1, hτ.2]

/-- The height is $C^2$ in $\theta$ when the angular cutoffs are $C^2$. -/
theorem height_contDiff {m : ℕ} (χ : Fin m → ℝ → ℝ) (hχ : ∀ j, ContDiff ℝ 2 (χ j))
    (v : Fin m → ℝ → Vec 2) (t : ℝ) : ContDiff ℝ 2 (height χ v t) := by
  have hn : ContDiff ℝ 2 normal := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Real.contDiff_cos
    · exact Real.contDiff_sin
  unfold height
  apply contDiff_const.add
  apply ContDiff.sum
  intro j _
  have hd : ContDiff ℝ 2 (fun θ => dot (normal θ) (v j t)) := by
    simpa only [gradientFunctional_apply, dot, mul_comm] using
      (gradientFunctional (v j t)).contDiff.comp hn
  exact (hχ j).mul (hd.sub contDiff_const)

/-- A field given by (`art:planar-field-formula`) near a point where $F$ is $C^2$ with
nonzero gradient agrees near it with the library field. -/
theorem eventuallyEq_field_of_formula {m : ℕ} {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (v : Fin m → ℝ → Vec 2)
    (w : Vec 2 → Vec 2) (x : Vec 2) (hFx : ContDiffAt ℝ 2 F x)
    (hgx : coordinateGradient F x ≠ 0)
    (hw : ∀ᶠ z in 𝓝 x, ∀ θ, normal θ = normalized (coordinateGradient F z) →
        w z = fieldFormula (fun j φ => χ j (normal φ)) v (F z) θ) :
    w =ᶠ[𝓝 x] PlanarObjectiveField.field hF χ v := by
  have hgC : ContinuousAt (coordinateGradient F) x := by
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hFx.fderiv_right (by norm_num)
    apply continuousAt_pi.mpr
    intro i
    exact (hfd.clm_apply contDiffAt_const).continuousAt
  filter_upwards [hw, hFx.eventually (by norm_num), hgC.eventually_ne hgx] with z hz hzC hz0
  have hgz := hasFDerivAt_coordinateGradient (hzC.differentiableAt (by norm_num))
  obtain ⟨θ, hθ⟩ := exists_angle _ (PlanarObjectiveField.normalized_sqNorm hz0)
  rw [hz θ hθ, field_eq_fieldFormula hF χ (fun j => (hχ j).differentiable (by simp)) v hgz θ hθ]

/-- Tangent preservation and the triangular form of $Dw$ at a smooth point (core of
`derivative_triangular`). -/
theorem field_derivative_triangular {m : ℕ} {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    (χ : Fin m → Vec 2 → ℝ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (v : Fin m → ℝ → Vec 2)
    (w : Vec 2 → Vec 2) (x : Vec 2) (hFx : ContDiffAt ℝ 2 F x)
    (hgx : coordinateGradient F x ≠ 0) (hvx : ∀ j, ContDiffAt ℝ 1 (v j) (F x))
    (hw : ∀ᶠ z in 𝓝 x, ∀ θ, normal θ = normalized (coordinateGradient F z) →
        w z = fieldFormula (fun j φ => χ j (normal φ)) v (F z) θ)
    (n T : Vec 2) (hn : n = normalized (coordinateGradient F x))
    (hT : T = PlanarAmbientFrame.rotate n) (a b e : ℝ) (ha : a = dot T (fderiv ℝ w x T))
    (hb : b = dot T (fderiv ℝ w x n)) (he : e = dot n (fderiv ℝ w x n)) :
    DifferentiableAt ℝ w x ∧ (∀ u, dot n u = 0 → dot n (fderiv ℝ w x u) = 0) ∧
      fderiv ℝ w x T = a • T ∧ fderiv ℝ w x n = b • T + e • n := by
  have hweq := eventuallyEq_field_of_formula hF χ hχ v w x hFx hgx hw
  have hdiffW := (PlanarObjectiveField.field_contDiffAt_smooth hF hχ hvx hFx hgx).differentiableAt
    (by norm_num)
  have hfd : fderiv ℝ w x = fderiv ℝ (PlanarObjectiveField.field hF χ v) x := hweq.fderiv_eq
  have hgn : 0 < ‖euclideanVector (coordinateGradient F x)‖ := norm_pos_iff.mpr (by
    intro h
    exact hgx (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) h))
  have hunit : sqNorm n = 1 := hn ▸ PlanarObjectiveField.normalized_sqNorm hgx
  have htan : ∀ u, dot n u = 0 → dot n (fderiv ℝ w x u) = 0 := by
    intro u hu
    have hu' : dot (coordinateGradient F x) u = 0 := by
      rw [hn, normalized, PlanarObjectiveField.dot_smul_first] at hu
      exact (mul_eq_zero.mp hu).resolve_left (inv_ne_zero hgn.ne')
    rw [hfd, hn, normalized, PlanarObjectiveField.dot_smul_first,
      PlanarObjectiveField.actual_field_derivative_preserves_tangent hF hχ hvx hFx hgx hu',
      mul_zero]
  refine ⟨hdiffW.congr_of_eventuallyEq hweq, htan, ?_, ?_⟩
  · have hnT : dot n T = 0 := hT ▸ PlanarAmbientFrame.rotate_orthogonal n
    have hrec := PlanarAmbientFrame.reconstruct hunit (fderiv ℝ w x T)
    rw [htan T hnT, zero_smul, zero_add, ← hT, ← ha] at hrec
    exact hrec.symm
  · have hrec := PlanarAmbientFrame.reconstruct hunit (fderiv ℝ w x n)
    rw [← hT, ← hb, ← he] at hrec
    rw [← hrec, add_comm]

/-- Proof of Lemma `art:planar-field`, the one-sided comparison of
`paper/appendices/planar_geometry.tex:168-173` (not a register item): "If a continuous function
$u$ on $[0,1]$ has $u'_+\le0$ on $[0,1)$, then $u(1)\le u(0)$." The right derivative is a
`HasDerivWithinAt` on `Ici θ`. (Proved with Mathlib's one-sided comparison
`image_le_of_deriv_right_le_deriv_boundary`.) -/
theorem one_sided_comparison (u u' : ℝ → ℝ) (hu : ContinuousOn u (Icc 0 1))
    (hu' : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u (u' θ) (Ici θ) θ)
    (hneg : ∀ θ ∈ Ico (0 : ℝ) 1, u' θ ≤ 0) : u 1 ≤ u 0 :=
  image_le_of_deriv_right_le_deriv_boundary hu hu' (B := fun _ => u 0) (B' := fun _ => 0)
    le_rfl continuousOn_const (fun θ _ => hasDerivWithinAt_const θ _ (u 0)) hneg (x := 1)
    (by norm_num)

/-- The comparison functions $\pm(H(\theta)-H(0))-A(\varphi(\theta)-\varphi(0)+2d\theta)$
(core of `comparison_functions`). -/
theorem comparison_core {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F) (x s : Vec 2) (d : ℝ)
    (φ H : ℝ → ℝ) (hφ : φ = fun θ => F (x + θ • s)) (hHcont : ContinuousOn H (Icc 0 1))
    (A : ℝ)
    (hbound : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt H (derivWithin H (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin H (Ioi θ) θ| ≤ A * |derivWithin φ (Ioi θ) θ| ∧
      A * |derivWithin φ (Ioi θ) θ| ≤ A * (derivWithin φ (Ioi θ) θ + 2 * d))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : ℝ → ℝ)
    (hu : u = fun θ => σ * (H θ - H 0) - A * (φ θ - φ 0 + 2 * d * θ)) :
    u 0 = 0 ∧
      (∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u
          (σ * derivWithin H (Ioi θ) θ - A * (derivWithin φ (Ioi θ) θ + 2 * d)) (Ici θ) θ ∧
        σ * derivWithin H (Ioi θ) θ - A * (derivWithin φ (Ioi θ) θ + 2 * d) ≤ 0) ∧
      u 1 ≤ 0 := by
  have hφc : ConvexOn ℝ univ φ := by
    have hc := hF.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x + s))
    rw [hφ]
    simpa only [AffineMap.lineMap_apply_module', add_sub_cancel_left, Function.comp_def,
      Set.preimage_univ, add_comm] using hc
  have hφcont : Continuous φ :=
    continuous_iff_continuousOn_univ.mpr (hφc.continuousOn isOpen_univ)
  have hderiv : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u
      (σ * derivWithin H (Ioi θ) θ - A * (derivWithin φ (Ioi θ) θ + 2 * d)) (Ici θ) θ := by
    intro θ hθ
    have hH' := (hbound θ hθ).1
    have hφr : HasDerivWithinAt φ (derivWithin φ (Ioi θ) θ) (Ici θ) θ :=
      (hφc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)).Ici_of_Ioi
    rw [hu]
    convert ((hH'.sub_const (H 0)).const_mul σ).sub
      (((hφr.sub_const (φ 0)).add ((hasDerivWithinAt_id θ (Ici θ)).const_mul (2 * d))).const_mul A)
      using 1
    ring
  have hnonpos : ∀ θ ∈ Ico (0 : ℝ) 1,
      σ * derivWithin H (Ioi θ) θ - A * (derivWithin φ (Ioi θ) θ + 2 * d) ≤ 0 := by
    intro θ hθ
    obtain ⟨-, h1, h2⟩ := hbound θ hθ
    have hσH : σ * derivWithin H (Ioi θ) θ ≤ |derivWithin H (Ioi θ) θ| := by
      rcases hσ with rfl | rfl
      · simpa using le_abs_self _
      · simpa using neg_le_abs _
    linarith
  have hu0 : u 0 = 0 := by
    rw [hu]
    ring
  refine ⟨hu0, fun θ hθ => ⟨hderiv θ hθ, hnonpos θ hθ⟩, ?_⟩
  have hucont : ContinuousOn u (Icc 0 1) := by
    rw [hu]
    exact ((hHcont.sub continuousOn_const).const_smul σ).sub
      (((hφcont.continuousOn.sub continuousOn_const).add
        (continuousOn_const.mul continuousOn_id)).const_smul A)
  have hle := one_sided_comparison u _ hucont hderiv hnonpos
  rwa [hu0] at hle

/-- $|H(1)-H(0)|\le2Ad$ (core of `log_determinant_increment`). -/
theorem increment_core {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F) (x s : Vec 2) (d : ℝ)
    (φ H : ℝ → ℝ) (hφ : φ = fun θ => F (x + θ • s)) (hHcont : ContinuousOn H (Icc 0 1))
    (hdesc : φ 1 ≤ φ 0) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt H (derivWithin H (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin H (Ioi θ) θ| ≤ A * |derivWithin φ (Ioi θ) θ| ∧
      A * |derivWithin φ (Ioi θ) θ| ≤ A * (derivWithin φ (Ioi θ) θ + 2 * d)) :
    |H 1 - H 0| ≤ 2 * A * d := by
  have hplus := (comparison_core hF x s d φ H hφ hHcont A hbound 1 (Or.inl rfl) _ rfl).2.2
  have hminus := (comparison_core hF x s d φ H hφ hHcont A hbound (-1) (Or.inr rfl) _ rfl).2.2
  simp only at hplus hminus
  rw [abs_le]
  constructor <;> nlinarith

/-- The descent estimate for a gradient that is $M$-Lipschitz in the Euclidean norm on a
convex set: $f(y+u)-f(y)-\nabla f(y)^Tu\le\frac M2\norm{u}^2$. -/
theorem descent_estimate {f : Vec 2 → ℝ} {V : Set (Vec 2)} (hV : Convex ℝ V)
    (hdiff : ∀ u ∈ V, DifferentiableAt ℝ f u) {M : ℝ}
    (hLip : ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient f u -
      coordinateGradient f u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    {y u : Vec 2} (hy : y ∈ V) (hyu : y + u ∈ V) :
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
    have hcs := PlanarCrossing.abs_dot_le_euclidean_norm
      (coordinateGradient f (y + τ • u) - coordinateGradient f y) u
    have hL := hLip _ (hmem τ hτ') y hy
    rw [add_sub_cancel_left, euclideanVector_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hτ.1] at hL
    have hsq := euclidean_norm_sq_eq u
    rw [dot_sub_left] at hcs
    have hun := norm_nonneg (euclideanVector u)
    have h1 : dot (coordinateGradient f (y + τ • u)) u - dot (coordinateGradient f y) u ≤
        M * (τ * ‖euclideanVector u‖) * ‖euclideanVector u‖ :=
      (le_abs_self _).trans (hcs.trans (mul_le_mul_of_nonneg_right hL hun))
    have he : M * (τ * ‖euclideanVector u‖) * ‖euclideanVector u‖ = M * τ * sqNorm u := by
      rw [← hsq]
      ring
    linarith
  have hcont : ContinuousOn φ (Icc 0 1) := fun τ hτ =>
    (hderiv τ hτ).continuousAt.continuousWithinAt
  have hle := one_sided_comparison φ _ hcont
    (fun τ hτ => (hderiv τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt) hnonpos
  simp only [φ, one_smul, one_mul, one_pow, zero_smul, add_zero, zero_mul, sub_self,
    mul_zero, zero_sub, sub_zero] at hle
  linarith

/-- The local convex-gradient estimate (core of `branch_cocoercivity`). -/
theorem cocoercivity_core (f : Vec 2 → ℝ) (V : Set (Vec 2)) (hVopen : IsOpen V)
    (hfconv : ConvexOn ℝ V f) (hfC : ContDiffOn ℝ 2 f V) (M : ℝ) (hM : 0 < M)
    (hLip : ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient f u -
      coordinateGradient f u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (B : Set (Vec 2)) (ρ : ℝ) (hρ : 0 < ρ)
    (hBV : ∀ u ∈ B, ∀ u' : Vec 2, ‖euclideanVector (u' - u)‖ < ρ → u' ∈ V)
    (x z : Vec 2) (hx : x ∈ B) (hz : z ∈ B) (hxz : ‖euclideanVector (z - x)‖ < ρ) :
    sqNorm (coordinateGradient f z - coordinateGradient f x) ≤
      2 * M * (f z - f x - dot (coordinateGradient f x) (z - x)) := by
  have hBV' : ∀ u ∈ B, u ∈ V := fun u hu => hBV u hu u (by simp [euclideanVector, hρ])
  have hxV := hBV' x hx
  have hzV := hBV' z hz
  have hdiff : ∀ u ∈ V, DifferentiableAt ℝ f u := fun u hu =>
    (hfC.contDiffAt (hVopen.mem_nhds hu)).differentiableAt (by norm_num)
  set p := coordinateGradient f x
  set q := coordinateGradient f z
  have hstepV : z - M⁻¹ • (q - p) ∈ V := by
    apply hBV z hz
    have hL := hLip z hzV x hxV
    rw [show z - M⁻¹ • (q - p) - z = (-M⁻¹) • (q - p) by module, euclideanVector_smul, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hM)]
    calc M⁻¹ * ‖euclideanVector (q - p)‖ ≤ M⁻¹ * (M * ‖euclideanVector (z - x)‖) :=
          mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hM.le)
      _ = ‖euclideanVector (z - x)‖ := by field_simp
      _ < ρ := hxz
  apply CenteredSmoothSublinear.bregman_lower_of_descent f p q x z M hM
  · simpa only [gradientFunctional_apply] using
      CenteredSmoothSublinear.supporting_inequality_on hfconv
        (hasFDerivAt_coordinateGradient (hdiff x hxV)) hxV hstepV
  · have hd := descent_estimate hfconv.1 hdiff hLip hzV
      (u := -M⁻¹ • (q - p)) (by simpa only [neg_smul, ← sub_eq_add_neg] using hstepV)
    simpa only [neg_smul, ← sub_eq_add_neg] using hd

/-- The tie point on the segment of a crossing pair (core of `crossing_tie_point`). -/
theorem tie_point_core {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F) (f : Fin 2 → Vec 2 → ℝ)
    (V : Set (Vec 2)) (hVconv : Convex ℝ V) (hVopen : IsOpen V)
    (hfC : ∀ i, ContDiffOn ℝ 2 (f i) V)
    (hFV : ∀ u ∈ V, IsGreatest (range fun i => f i u) (F u)) (w : Vec 2 → Vec 2)
    (hcommon : ∀ p ∈ V, ∀ a ∈ subdifferential F p, ∀ b ∈ subdifferential F p,
      dot a (w p) = dot b (w p))
    (x z : Vec 2) (hx : x ∈ V) (hz : z ∈ V)
    (i j : Fin 2) (hij : i ≠ j) (hi : f i x = F x) (hj : f j z = F z) :
    ∃ p ∈ segment ℝ x z, f i p = F p ∧ f j p = F p ∧
      dot (coordinateGradient (f j) p - coordinateGradient (f i) p) (w p) = 0 := by
  have hrep : ∀ u ∈ V, LocalFiniteMax F f u := by
    intro u hu
    filter_upwards [hVopen.mem_nhds hu] with y hy
    exact hFV y hy
  have hdiff : ∀ k, ∀ u ∈ V, DifferentiableAt ℝ (f k) u := fun k u hu =>
    ((hfC k).contDiffAt (hVopen.mem_nhds hu)).differentiableAt (by norm_num)
  have hseg : segment ℝ x z ⊆ V := hVconv.segment_subset hx hz
  have hci : ContinuousOn (f i) (segment ℝ x z) :=
    fun p hp => (hdiff i p (hseg hp)).continuousAt.continuousWithinAt
  have hcj : ContinuousOn (f j) (segment ℝ x z) :=
    fun p hp => (hdiff j p (hseg hp)).continuousAt.continuousWithinAt
  have hix : f j x ≤ f i x := by rw [hi]; exact (hFV x hx).2 (mem_range_self j)
  have hjz : f i z ≤ f j z := by rw [hj]; exact (hFV z hz).2 (mem_range_self i)
  obtain ⟨p, hp', htie⟩ := PlanarCrossing.exists_tie_on_segment (F := F) hci hcj hix hjz
  have hpV := hseg hp'
  have hpi : f i p = F p := by
    obtain ⟨k, hk⟩ := (hFV p hpV).1
    have hkij : k = i ∨ k = j := by omega
    rcases hkij with rfl | rfl
    · exact hk
    · exact htie.trans hk
  have hpj : f j p = F p := htie.symm.trans hpi
  have hsupp (k : Fin 2) (hk : f k p = F p) : coordinateGradient (f k) p ∈ subdifferential F p :=
    active_gradient_supports hF (hrep p hpV)
      (fun l => hasFDerivAt_coordinateGradient (hdiff l p hpV)) (mem_activeIndices.mpr hk)
  refine ⟨p, hp', hpi, hpj, ?_⟩
  rw [dot_sub_left, hcommon p hpV _ (hsupp j hpj) _ (hsupp i hpi), sub_self]

/-- The numerator bound of a crossing pair (core of `crossing_numerator`). -/
theorem crossing_core {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F) (f : Fin 2 → Vec 2 → ℝ)
    (V : Set (Vec 2)) (hVconv : Convex ℝ V) (hVopen : IsOpen V)
    (hfC : ∀ i, ContDiffOn ℝ 2 (f i) V)
    (hFV : ∀ u ∈ V, IsGreatest (range fun i => f i u) (F u))
    (M Hb : ℝ) (hM : 0 ≤ M) (hHb : 0 ≤ Hb)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (hgradB : ∀ i, ∀ u ∈ V, ‖euclideanVector (coordinateGradient (f i) u)‖ ≤ Hb)
    (w : Vec 2 → Vec 2) (Bw G : ℝ) (hBw : 0 ≤ Bw) (hG : 0 ≤ G)
    (hwLip : ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (w u - w u')‖ ≤ Bw * ‖euclideanVector (u - u')‖)
    (hwB : ∀ u ∈ V, ‖euclideanVector (w u)‖ ≤ G)
    (hcommon : ∀ p ∈ V, ∀ a ∈ subdifferential F p, ∀ b ∈ subdifferential F p,
      dot a (w p) = dot b (w p))
    (x z g h : Vec 2) (hx : x ∈ V) (hz : z ∈ V)
    (hgx : HasFDerivAt F (gradientFunctional g) x) (hhz : HasFDerivAt F (gradientFunctional h) z)
    (i j : Fin 2) (hij : i ≠ j) (hi : f i x = F x) (hj : f j z = F z) :
    |dot (h - g) (w z)| ≤ (2 * M * G + 2 * Hb * Bw) * ‖euclideanVector (z - x)‖ := by
  have hrep : ∀ u ∈ V, LocalFiniteMax F f u := by
    intro u hu
    filter_upwards [hVopen.mem_nhds hu] with y hy
    exact hFV y hy
  have hdiff : ∀ k, ∀ u ∈ V, DifferentiableAt ℝ (f k) u := fun k u hu =>
    ((hfC k).contDiffAt (hVopen.mem_nhds hu)).differentiableAt (by norm_num)
  have hgi := PlanarCrossing.actual_gradient_eq_active_branch hF (hrep x hx)
    (fun k => hdiff k x hx) hgx hi
  have hhj := PlanarCrossing.actual_gradient_eq_active_branch hF (hrep z hz)
    (fun k => hdiff k z hz) hhz hj
  obtain ⟨p, hp, _, _, horth⟩ := tie_point_core hF f V hVconv hVopen hfC hFV w hcommon x z hx hz
    i j hij hi hj
  have hpV := hVconv.segment_subset hx hz hp
  obtain ⟨hpx, hzp⟩ := segment_euclidean_dist hp
  have hr := norm_nonneg (euclideanVector (z - x))
  have hri : ‖euclideanVector (coordinateGradient (f i) p - g)‖ ≤
      M * ‖euclideanVector (z - x)‖ := by
    rw [← hgi]
    exact (hLip i p hpV x hx).trans (mul_le_mul_of_nonneg_left hpx hM)
  have hrj : ‖euclideanVector (h - coordinateGradient (f j) p)‖ ≤
      M * ‖euclideanVector (z - x)‖ := by
    rw [← hhj]
    exact (hLip j z hz p hpV).trans (mul_le_mul_of_nonneg_left hzp hM)
  have hjump : ‖euclideanVector (coordinateGradient (f j) p - coordinateGradient (f i) p)‖ ≤
      2 * Hb := by
    rw [euclideanVector_sub]
    calc _ ≤ ‖euclideanVector (coordinateGradient (f j) p)‖ +
          ‖euclideanVector (coordinateGradient (f i) p)‖ := norm_sub_le _ _
      _ ≤ Hb + Hb := add_le_add (hgradB j p hpV) (hgradB i p hpV)
      _ = 2 * Hb := by ring
  have hchange : ‖euclideanVector (w z - w p)‖ ≤ Bw * ‖euclideanVector (z - x)‖ :=
    (hwLip z hz p hpV).trans (mul_le_mul_of_nonneg_left hzp hBw)
  have hb := PlanarCrossing.crossing_numerator_bound hM hG (by positivity : (0 : ℝ) ≤ 2 * Hb)
    hBw hr (show h - g = (h - coordinateGradient (f j) p) +
      (coordinateGradient (f j) p - coordinateGradient (f i) p) +
        (coordinateGradient (f i) p - g) by abel)
    horth hri hrj (hwB z hz) hjump hchange
  convert hb using 1

/-- The two pairings of a crossing pair (core of `crossing_pairings`). -/
theorem crossing_pairings_core {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F) (f : Fin 2 → Vec 2 → ℝ)
    (V : Set (Vec 2)) (hVopen : IsOpen V) (hfC : ∀ i, ContDiffOn ℝ 2 (f i) V)
    (hFV : ∀ u ∈ V, IsGreatest (range fun i => f i u) (F u)) (M : ℝ)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (x z g h : Vec 2) (hx : x ∈ V) (hz : z ∈ V)
    (hgx : HasFDerivAt F (gradientFunctional g) x) (hhz : HasFDerivAt F (gradientFunctional h) z)
    (i j : Fin 2) (hi : f i x = F x) (hj : f j z = F z)
    (s y : Vec 2) (hs : s = z - x) (hy : y = h - g) (d t : ℝ) (hd : d = -dot g s)
    (ht : t = dot y s) (r : Vec 2)
    (hr : r = coordinateGradient (f j) z - coordinateGradient (f j) x) :
    ‖euclideanVector r‖ ≤ M * ‖euclideanVector s‖ ∧
      dot (coordinateGradient (f i) x) s = -d ∧
      dot (coordinateGradient (f j) x) s = t - d - dot r s := by
  have hrep : ∀ u ∈ V, LocalFiniteMax F f u := by
    intro u hu
    filter_upwards [hVopen.mem_nhds hu] with y hy
    exact hFV y hy
  have hdiff : ∀ k, ∀ u ∈ V, DifferentiableAt ℝ (f k) u := fun k u hu =>
    ((hfC k).contDiffAt (hVopen.mem_nhds hu)).differentiableAt (by norm_num)
  have hgi := PlanarCrossing.actual_gradient_eq_active_branch hF (hrep x hx)
    (fun k => hdiff k x hx) hgx hi
  have hhj := PlanarCrossing.actual_gradient_eq_active_branch hF (hrep z hz)
    (fun k => hdiff k z hz) hhz hj
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, hs]
    exact hLip j z hz x hx
  · rw [hgi, hd, neg_neg]
  · have hfjx : coordinateGradient (f j) x = h - r := by rw [hr, ← hhj]; abel
    rw [hfjx, ht, hd, hy, dot_sub_left, dot_sub_left]
    ring

/-! ### Lemma `art:planar-field` -/

/-- Item `A/planar_geometry/lemma/art:planar-field` (`paper/appendices/planar_geometry.tex:7-37`),
Lemma `art:planar-field`, "One field with all endpoint estimates", including its displays
`A/planar_geometry/disp/001` (lines 25-28) and `A/planar_geometry/disp/002` (lines 30-34).

Let $F:\R^2\to\R$ be finite and convex with minimum $F_*$, and let $C\subset\{F=\ell\}$ be a
nonempty compact set, where $\ell>F_*$. Suppose the boundary of $\{F\le\ell\}$ contains no
nontrivial segment and every point of $C$ is non-affine-critical and has the smooth or regular
convex two-branch structure in Theorem `art:planar-cluster`. Fix valid Armijo--weak-Wolfe
constants. There exist an open neighborhood $U\supset C$, a compact buffer $Q\supset\overline U$,
a field $w$ defined on a neighborhood of $Q$, and constants $\eta,\kappa,\delta>0$,
$C_0,C_1,L\ge0$ such that:
1. The field is locally Lipschitz, bounded on $Q$, and every $g\in\partial F(p)$, $p\in Q$,
   satisfies $g^Tw(p)\ge\eta$. All subgradients at a fixed point have the same pairing with
   $w(p)$.
2. For every eligible pair $x,z\in U$ with $\norm{s}<\delta$, its entire segment lies in $Q$ and
   \[ |\det(s,w(x+\theta s))|\ge\kappa\norm{s}\quad(0\le\theta\le1),\qquad
      (y^Tw(z))^2/t\le C_0. \]
3. For every such pair there are $\lambda>0$ and $\beta\in\R$ with
   \[ w(z)=\lambda w(x)+\beta s,\qquad |\log\lambda|\le C_1d,\qquad
      d\le1\ \Longrightarrow\ \lambda^2\le1+Ld. \]
All neighborhoods, constants and the field are chosen before the endpoint pair or any BFGS
matrix (they are existentially quantified before the pair).

"Defined on a neighborhood of $Q$" and "locally Lipschitz" are stated as: $w$ is locally
Lipschitz at every point of an open set $N\supset Q$. The proof is the library's
`PlanarAllPairs.source_all_endpoint_estimates` (the same construction as the paper's proof),
with `hregular` converted to the library's form by `regularity_of_literal`; boundedness on $Q$
follows from continuity on the compact $Q$. -/
theorem planar_field (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    ∃ (U Q : Set (Vec 2)) (w : Vec 2 → Vec 2) (η κ δ C₀ C₁ L : ℝ),
      IsOpen U ∧ C ⊆ U ∧ IsCompact Q ∧ closure U ⊆ Q ∧
      0 < η ∧ 0 < κ ∧ 0 < δ ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ L ∧
      (∃ N : Set (Vec 2), IsOpen N ∧ Q ⊆ N ∧
        ∀ p ∈ N, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 p, LipschitzOnWith K w V) ∧
      (∃ B : ℝ, ∀ p ∈ Q, ‖euclideanVector (w p)‖ ≤ B) ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, η ≤ dot g (w p)) ∧
      (∀ p ∈ Q, ∀ g ∈ subdifferential F p, ∀ g' ∈ subdifferential F p,
        dot g (w p) = dot g' (w p)) ∧
      ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
        ‖euclideanVector (z - x)‖ < δ →
          (∀ θ ∈ Icc (0 : ℝ) 1, x + θ • (z - x) ∈ Q ∧
            κ * ‖euclideanVector (z - x)‖ ≤ |pairDet (z - x) (w (x + θ • (z - x)))|) ∧
          (dot (h - g) (w z)) ^ 2 / dot (h - g) (z - x) ≤ C₀ ∧
          ∃ lam β : ℝ, 0 < lam ∧ w z = lam • w x + β • (z - x) ∧
            |Real.log lam| ≤ C₁ * (-dot g (z - x)) ∧
            (-dot g (z - x) ≤ 1 → lam ^ 2 ≤ 1 + L * (-dot g (z - x))) := by
  obtain ⟨m, χ, v, _hχ, U, Q, hU, hCU, hUQ, hQ, η, κ, δ, C₁, L, C₀, hη, hκ, hδ, hC₁, hL, hC₀,
    hLip, hvis, hcommon, hpairs⟩ :=
    PlanarAllPairs.source_all_endpoint_estimates hF hCcpt (fun x hx => hCℓ hx) hstrict
      (fun p hp => regularity_of_literal (hregular p hp)) hnoncrit hc₁ hc₂
  obtain ⟨N, hN, hQN, hLipN⟩ := PlanarObjectiveField.exists_open_local_lipschitz_extension hLip
  have hcont : ContinuousOn (fun p => euclideanVector (PlanarObjectiveField.field hF χ v p)) Q := by
    intro p hp
    obtain ⟨K, V, hV, hKV⟩ := hLip p hp
    exact ((PiLp.continuous_equiv_symm _ _).continuousAt.comp
      (hKV.continuousOn.continuousAt hV)).continuousWithinAt
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hcont
  refine ⟨U, Q, PlanarObjectiveField.field hF χ v, η, κ, δ, C₀, C₁, L, hU, hCU, hQ, hUQ, hη, hκ,
    hδ, hC₀, hC₁, hL, ⟨N, hN, hQN, hLipN⟩, ⟨B, hB⟩, hvis, hcommon, ?_⟩
  intro x hx z hz g h hp hs
  exact hpairs x hx z hz g h hp hs

/-! ### Corner motion -/

/-- Proof of Lemma `art:planar-field`, undisplayed claims of
`paper/appendices/planar_geometry.tex:40-43` (not a register item): "At a nonsmooth point of
$C$, the local branch-value map $x\mapsto(f_1(x),f_2(x))$ has nonsingular derivative. The
inverse function theorem gives a $C^2$ curve $p_j(t)$ characterized by
$f_1(p_j(t))=f_2(p_j(t))=t$ for $t$ near $\ell$." The corner $c\in C$ comes with the
two-branch data of `hregular` at $c$ (the open convex set `V` and the branches `f₁`, `f₂`).
The branch-value map has an invertible derivative at $c$, and there is a $C^2$ curve $p$ with
$p(\ell)=c$ and $f_1(p(t))=f_2(p(t))=t$ near $\ell$, which near $c$ is the only point where the
two branches agree (the characterization). -/
theorem corner_curve (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
    (_hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (c : Vec 2) (hc : c ∈ C) (_hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (_hf₁ : ConvexOn ℝ V f₁) (_hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (_hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c]) :
    (∃ L : Vec 2 ≃L[ℝ] Vec 2, HasFDerivAt (fun z => ![f₁ z, f₂ z]) (L : Vec 2 →L[ℝ] Vec 2) c) ∧
      ∃ p : ℝ → Vec 2, p ℓ = c ∧ ContDiffAt ℝ 2 p ℓ ∧
        (∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) ∧
        ∀ᶠ z in 𝓝 c, f₁ z = f₂ z → z = p (f₁ z) := by
  set f : Fin 2 → Vec 2 → ℝ := ![f₁, f₂] with hfdef
  have hC2 (i : Fin 2) : ContDiffAt ℝ 2 (f i) c := by
    fin_cases i
    · exact hC₁.contDiffAt (hV.mem_nhds hcV)
    · exact hC₂.contDiffAt (hV.mem_nhds hcV)
  have hg (i : Fin 2) := hasFDerivAt_coordinateGradient ((hC2 i).differentiableAt (by norm_num))
  have hcℓ : F c = ℓ := hCℓ hc
  have hd : pairDet (coordinateGradient (f 0) c) (coordinateGradient (f 1) c) ≠ 0 :=
    pairDet_ne_zero_of_independent hind
  obtain ⟨p, hpℓ, hpC, hpdef, hpinv⟩ := exists_corner_chart hC2 (hg 0) (hg 1) hd
    (hact₁.trans hcℓ) (hact₂.trans hcℓ)
  refine ⟨⟨rowEquiv _ _ hd, ?_⟩, p, hpℓ, hpC, ?_, ?_⟩
  · have h := branchValues_hasFDerivAt (hg 0) (hg 1) hd
    convert h using 1
    funext z
    ext i
    fin_cases i <;> rfl
  · filter_upwards [hpdef] with t ht
    exact ⟨ht 0, ht 1⟩
  · filter_upwards [hpinv] with z hz heq
    apply hz
    intro i
    fin_cases i
    · rfl
    · exact heq.symm

/-- Item `A/planar_geometry/disp/003` (`paper/appendices/planar_geometry.tex:45-48`), equation
`art:corner-velocity`, in the proof of Lemma `art:planar-field`.

Under the assumptions of the lemma, at a nonsmooth point $c$ of $C$ with the two-branch data of
`hregular` at $c$ (branches $f_1,f_2$ on the open convex set $V$), let $p_j$ be a $C^2$ curve
with $p_j(\ell)=c$ and $f_1(p_j(t))=f_2(p_j(t))=t$ for $t$ near $\ell$ (as given by
`corner_curve`), and $v_j=p_j'$. Then $v_j$ is $C^1$ at $\ell$ and, for $t$ near $\ell$,
\[ \nabla f_1(p_j(t))^Tv_j(t)=\nabla f_2(p_j(t))^Tv_j(t)=1. \] -/
theorem corner_velocity (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (c : Vec 2) (_hc : c ∈ C) (_hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (_hf₁ : ConvexOn ℝ V f₁) (_hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (_hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (_hact₁ : f₁ c = F c) (_hact₂ : f₂ c = F c)
    (_hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t) (v : ℝ → Vec 2) (hv : v = deriv p) :
    ContDiffAt ℝ 1 v ℓ ∧ ∀ᶠ t in 𝓝 ℓ,
      dot (coordinateGradient f₁ (p t)) (v t) = 1 ∧
        dot (coordinateGradient f₂ (p t)) (v t) = 1 := by
  subst hv
  refine ⟨curve_velocity_contDiffAt hpC, ?_⟩
  set f : Fin 2 → Vec 2 → ℝ := ![f₁, f₂] with hfdef
  have hpt : Tendsto p (𝓝 ℓ) (𝓝 c) := by
    simpa only [ContinuousAt, hpℓ] using hpC.continuousAt
  have hbranch : ∀ᶠ t in 𝓝 ℓ, ∀ i, ContDiffAt ℝ 2 (f i) (p t) := by
    filter_upwards [hpt.eventually (hV.mem_nhds hcV)] with t ht i
    fin_cases i
    · exact hC₁.contDiffAt (hV.mem_nhds ht)
    · exact hC₂.contDiffAt (hV.mem_nhds ht)
  have hpdef' : ∀ᶠ t in 𝓝 ℓ, ∀ i, f i (p t) = t := by
    filter_upwards [hpdef] with t ht i
    fin_cases i
    · exact ht.1
    · exact ht.2
  filter_upwards [hbranch, hpC.eventually (by norm_num), hpdef'.eventually_nhds] with t ht hct he
  have hr := curve_velocity_pairing ((hct.differentiableAt (by norm_num)).hasDerivAt)
    (fun i => hasFDerivAt_coordinateGradient ((ht i).differentiableAt (by norm_num))) he
  exact ⟨hr 0, hr 1⟩

/-! ### The field near the switching curves -/

/-- Item `A/planar_geometry/disp/006` (`paper/appendices/planar_geometry.tex:90-92`), equation
`art:planar-corner-field`, in the proof of Lemma `art:planar-field`: the pointwise
calculation. "Near the $j$th switching curve the relevant cutoff equals one and
all others vanish. Consequently $h=n^Tv_j$, $h_\theta=T^Tv_j$, and
\[ w(x)=v_j(F(x)). \]"
Under the assumptions of the lemma, with angular cutoffs $\chi_j$ with disjoint supports, at a
smooth point $x$ with gradient $g$, normal angle $\theta$ ($n(\theta)=g/\norm g$) and
$w(x)$ given by (`art:planar-field-formula`): if $\chi_j=1$ near $\theta$, then
$h(F(x),\theta)=n(\theta)^Tv_j(F(x))$, $h_\theta(F(x),\theta)=T(\theta)^Tv_j(F(x))$ and
$w(x)=v_j(F(x))$. `corner_field` gives the neighborhood statement for the constructed field. -/
theorem corner_field_formula (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    {m : ℕ} (χ : Fin m → ℝ → ℝ)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (w : Vec 2 → Vec 2) (x g : Vec 2)
    (_hg : HasFDerivAt F (gradientFunctional g) x) (θ : ℝ) (_hθ : normal θ = normalized g)
    (hw : w x = fieldFormula χ v (F x) θ) (j : Fin m) (hplateau : ∀ᶠ φ in 𝓝 θ, χ j φ = 1) :
    height χ v (F x) θ = dot (normal θ) (v j (F x)) ∧
      deriv (height χ v (F x)) θ = dot (tangent θ) (v j (F x)) ∧ w x = v j (F x) := by
  have hsingle : ∀ φ, χ j φ = 1 → height χ v (F x) φ = dot (normal φ) (v j (F x)) := by
    intro φ hφ
    have hother : ∀ i, i ≠ j → χ i φ = 0 := by
      intro i hij
      by_contra hne
      exact Set.disjoint_left.mp (hχsupp hij) hne (by rw [Function.mem_support, hφ]; norm_num)
    unfold height
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hother i hij, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h), hφ]
    ring
  have hh : height χ v (F x) θ = dot (normal θ) (v j (F x)) := hsingle θ hplateau.self_of_nhds
  have hd : HasDerivAt (fun φ => dot (normal φ) (v j (F x))) (dot (tangent θ) (v j (F x))) θ := by
    have hc := (gradientFunctional (v j (F x))).hasFDerivAt.comp_hasDerivAt θ (normal_hasDerivAt θ)
    simpa only [gradientFunctional_apply, dot, mul_comm] using hc
  have hderiv : deriv (height χ v (F x)) θ = dot (tangent θ) (v j (F x)) := by
    apply HasDerivAt.deriv
    apply hd.congr_of_eventuallyEq
    filter_upwards [hplateau] with φ hφ
    exact hsingle φ hφ
  refine ⟨hh, hderiv, ?_⟩
  rw [hw, fieldFormula, hh, hderiv]
  exact reconstruct θ (v j (F x))

/-- Item `A/planar_geometry/disp/006` (`paper/appendices/planar_geometry.tex:90-92`), equation
`art:planar-corner-field`, in the proof of Lemma `art:planar-field`: the neighborhood
statement. "Near the $j$th switching curve the relevant cutoff equals one \dots\
$w(x)=v_j(F(x))$. This holds on both smooth sides in a whole neighborhood of the curve.
Use the same formula on the curve itself."

Under the assumptions of the lemma, at a nonsmooth point $c$ of $C$ with its two-branch data,
its curve $p$ (as in `corner_velocity`) and $v_j=p'$, let the smooth ambient cutoffs
$\chi_j$ have disjoint supports and let $\chi_j=1$ on a neighborhood of the normal arc at $c$
(`normalSector`: the unit vectors of the cone generated by the two active gradients). Then
near $c$ every subgradient is nonzero and its unit normal lies in the plateau
$\{\chi_j=1\}$, and the field $w$ of the proof satisfies $w(z)=v_j(F(z))$ for all $z$ near $c$,
smooth or not. -/
theorem corner_field (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
    (_hCcpt : IsCompact C) (hCℓ : C ⊆ {x | F x = ℓ}) (_hℓ : Fstar < ℓ)
    (_hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y)
    (_hnoncrit : ∀ p ∈ C, ¬IsAffineCritical F p)
    (_hregular : ∀ p ∈ C,
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
      (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
        ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
        (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
        LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p]))
    (c₁ c₂ : ℝ) (_hc₁ : 0 < c₁) (_hc₁₂ : c₁ < c₂) (_hc₂ : c₂ < 1)
    (c : Vec 2) (hc : c ∈ C) (_hcns : ¬DifferentiableAt ℝ F c)
    (V : Set (Vec 2)) (hV : IsOpen V) (hcV : c ∈ V) (f₁ f₂ : Vec 2 → ℝ)
    (_hf₁ : ConvexOn ℝ V f₁) (_hf₂ : ConvexOn ℝ V f₂) (hC₁ : ContDiffOn ℝ 2 f₁ V)
    (hC₂ : ContDiffOn ℝ 2 f₂ V) (hmax : ∀ z ∈ V, F z = max (f₁ z) (f₂ z))
    (hact₁ : f₁ c = F c) (hact₂ : f₂ c = F c)
    (_hind : LinearIndependent ℝ ![coordinateGradient f₁ c, coordinateGradient f₂ c])
    (p : ℝ → Vec 2) (hpℓ : p ℓ = c) (hpC : ContDiffAt ℝ 2 p ℓ)
    (hpdef : ∀ᶠ t in 𝓝 ℓ, f₁ (p t) = t ∧ f₂ (p t) = t)
    {m : ℕ} (χ : Fin m → Vec 2 → ℝ)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (j : Fin m) (hvj : v j = deriv p)
    (hplateau : ∀ᶠ u in 𝓝ˢ (normalSector (coordinateGradient f₁ c)
      (coordinateGradient f₂ c)), χ j u = 1)
    (w : Vec 2 → Vec 2) (hw : w = PlanarObjectiveField.field hF χ v) :
    (∀ᶠ z in 𝓝 c, ∀ a ∈ subdifferential F z, a ≠ 0 ∧ ∀ᶠ u in 𝓝 (normalized a), χ j u = 1) ∧
      ∀ᶠ z in 𝓝 c, w z = v j (F z) := by
  set f : Fin 2 → Vec 2 → ℝ := ![f₁, f₂] with hfdef
  have hC2 (i : Fin 2) : ContDiffAt ℝ 2 (f i) c := by
    fin_cases i
    · exact hC₁.contDiffAt (hV.mem_nhds hcV)
    · exact hC₂.contDiffAt (hV.mem_nhds hcV)
  have hg (i : Fin 2) := hasFDerivAt_coordinateGradient ((hC2 i).differentiableAt (by norm_num))
  have hrep : LocalFiniteMax F f c := by
    filter_upwards [hV.mem_nhds hcV] with z hz
    exact isGreatest_of_max f (hmax z hz)
  have hact : ∀ i, f i c = F c := by
    intro i
    fin_cases i
    · exact hact₁
    · exact hact₂
  have hpdef' : ∀ᶠ t in 𝓝 ℓ, ∀ i, f i (p t) = t := by
    filter_upwards [hpdef] with t ht i
    fin_cases i
    · exact ht.1
    · exact ht.2
  have hcℓ : F c = ℓ := hCℓ hc
  have hrate : ∀ i, dot (coordinateGradient (f i) c) (v j (F c)) = 1 := by
    have hgrad (i : Fin 2) : HasFDerivAt (f i)
        (gradientFunctional (coordinateGradient (f i) c)) (p ℓ) := by rw [hpℓ]; exact hg i
    have h := curve_velocity_pairing ((hpC.differentiableAt (by norm_num)).hasDerivAt) hgrad
      hpdef'
    rw [hvj, hcℓ]
    exact h
  subst hw
  exact ⟨all_supports_in_corner_plateau hF hrep hg hact hrate hplateau,
    PlanarObjectiveField.field_eventually_eq_corner_velocity hF hrep hg hact hrate v hχsupp
      hplateau⟩

/-! ### Visibility, tangent cancellation and the derivative of the field -/

/-- Item `A/planar_geometry/disp/007` (`paper/appendices/planar_geometry.tex:98-100`), in the
proof of Lemma `art:planar-field`: at a smooth point,
\[ \nabla F(x)^Tw(x)=\norm{\nabla F(x)}h(F(x),\theta(x))>0. \]
Under the assumptions of the lemma, with angular cutoffs $0\le\chi_j\le1$ with disjoint
supports whose supports satisfy $n^Tv_j>0$ at the level $F(x)$, at a point $x$ with gradient
$g\ne0$ and normal angle $\theta$, and with $w(x)$ given by (`art:planar-field-formula`). -/
theorem smooth_pairing (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    {m : ℕ} (χ : Fin m → ℝ → ℝ) (hχ01 : ∀ j φ, χ j φ ∈ Icc (0 : ℝ) 1)
    (hχsupp : Pairwise fun i j => Disjoint (Function.support (χ i)) (Function.support (χ j)))
    (v : Fin m → ℝ → Vec 2) (w : Vec 2 → Vec 2) (x g : Vec 2)
    (_hg : HasFDerivAt F (gradientFunctional g) x) (hg0 : g ≠ 0)
    (θ : ℝ) (hθ : normal θ = normalized g) (hw : w x = fieldFormula χ v (F x) θ)
    (hpos : ∀ j, χ j θ ≠ 0 → 0 < dot (normal θ) (v j (F x))) :
    dot g (w x) = ‖euclideanVector g‖ * height χ v (F x) θ ∧
      0 < ‖euclideanVector g‖ * height χ v (F x) θ := by
  have hgn : 0 < ‖euclideanVector g‖ := norm_pos_iff.mpr (by
    intro he
    exact hg0 (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => fun i => z i) he))
  have hgeq : g = ‖euclideanVector g‖ • normal θ := by
    rw [hθ, normalized, smul_smul, mul_inv_cancel₀ hgn.ne', one_smul]
  have hpair : dot (normal θ) (w x) = height χ v (F x) θ := by
    rw [hw]
    exact normal_pairing_angularFrame (height χ v (F x)) (deriv (height χ v (F x))) θ
  have hheight : 0 < height χ v (F x) θ := by
    by_cases he : ∃ i, χ i θ ≠ 0
    · obtain ⟨i, hi⟩ := he
      have hother : ∀ k, k ≠ i → χ k θ = 0 := by
        intro k hki
        by_contra hne
        exact Set.disjoint_left.mp (hχsupp hki) hne hi
      have heq : height χ v (F x) θ = 1 + χ i θ * (dot (normal θ) (v i (F x)) - 1) := by
        unfold height
        rw [Finset.sum_eq_single i (fun k _ hki => by rw [hother k hki, zero_mul])
          (fun h => absurd (Finset.mem_univ i) h)]
      rw [heq]
      have hc := hχ01 i θ
      have hcpos : 0 < χ i θ := lt_of_le_of_ne hc.1 (fun h => hi h.symm)
      have hp := mul_pos hcpos (hpos i hi)
      nlinarith [hc.2]
    · push_neg at he
      simp only [height, he, zero_mul, Finset.sum_const_zero, add_zero]
      norm_num
  refine ⟨?_, mul_pos hgn hheight⟩
  conv_lhs => rw [hgeq]
  change dotProduct (‖euclideanVector g‖ • normal θ) (w x) = _
  rw [smul_dotProduct]
  change ‖euclideanVector g‖ * dot (normal θ) (w x) = _
  rw [hpair]

/-- Item `A/planar_geometry/disp/008` (`paper/appendices/planar_geometry.tex:110-112`), equation
`art:planar-tangent-cancellation`, in the proof of Lemma `art:planar-field`:
\[ \partial_\theta(hn+h_\theta T)=(h+h_{\theta\theta})T. \]
Under the assumptions of the lemma, for $C^2$ angular cutoffs $\chi_j$, any velocities and any
level $t$, with $h=h(t,\cdot)$ of (`art:planar-height`), at every angle $\theta$. -/
theorem tangent_cancellation (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    {m : ℕ} (χ : Fin m → ℝ → ℝ) (hχ : ∀ j, ContDiff ℝ 2 (χ j))
    (v : Fin m → ℝ → Vec 2) (t : ℝ) (h : ℝ → ℝ) (hh : h = height χ v t) (θ : ℝ) :
    HasDerivAt (fun φ => h φ • normal φ + deriv h φ • tangent φ)
      ((h θ + deriv (deriv h) θ) • tangent θ) θ := by
  have hC : ContDiff ℝ 2 h := hh ▸ height_contDiff χ hχ v t
  have hC' : ContDiff ℝ (1 + 1) h := by simpa using hC
  obtain ⟨hdiff, -, hderiv⟩ := contDiff_succ_iff_deriv.mp hC'
  have h1 : HasDerivAt h (deriv h θ) θ := (hdiff θ).hasDerivAt
  have h2 : HasDerivAt (deriv h) (deriv (deriv h) θ) θ :=
    ((hderiv.differentiable le_rfl) θ).hasDerivAt
  exact angularFrame_hasDerivAt h (deriv h) θ (deriv h θ) (deriv (deriv h) θ) h1 h2 rfl

/-- Item `A/planar_geometry/disp/009` (`paper/appendices/planar_geometry.tex:115-117`), in the
proof of Lemma `art:planar-field`: "Thus at a smooth point the derivative of $w$ maps the
tangent line of a level curve into that same line. In the orthonormal basis $(T,n)$,
\[ Dw=\begin{pmatrix}a&b\\0&e\end{pmatrix} \]
with bounded coefficients." This theorem is the pointwise part; `derivative_coefficients_bounded`
is the uniform bound.

Under the assumptions of the lemma, with smooth ambient cutoffs, at a point $x$ where $F$ is
$C^2$ with $\nabla F(x)\ne0$, the velocities are $C^1$ at $F(x)$, and $w$ is given by
(`art:planar-field-formula`) near $x$: with $n=\nabla F(x)/\norm{\nabla F(x)}$, $T$ the rotated
normal ($T(\theta(x))$), $a=T^TDwT$, $b=T^TDw\,n$, $e=n^TDw\,n$, the field is differentiable at
$x$, $Dw$ maps $\{u:n^Tu=0\}$ into itself, $Dw\,T=aT$ and $Dw\,n=bT+en$. -/
theorem derivative_triangular (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (w : Vec 2 → Vec 2) (x : Vec 2) (hFx : ContDiffAt ℝ 2 F x)
    (hgx : coordinateGradient F x ≠ 0) (hvx : ∀ j, ContDiffAt ℝ 1 (v j) (F x))
    (hw : ∀ᶠ z in 𝓝 x, ∀ θ, normal θ = normalized (coordinateGradient F z) →
        w z = fieldFormula (fun j φ => χ j (normal φ)) v (F z) θ)
    (n T : Vec 2) (hn : n = normalized (coordinateGradient F x))
    (hT : T = PlanarAmbientFrame.rotate n) (a b e : ℝ) (ha : a = dot T (fderiv ℝ w x T))
    (hb : b = dot T (fderiv ℝ w x n)) (he : e = dot n (fderiv ℝ w x n)) :
    DifferentiableAt ℝ w x ∧ (∀ u, dot n u = 0 → dot n (fderiv ℝ w x u) = 0) ∧
      fderiv ℝ w x T = a • T ∧ fderiv ℝ w x n = b • T + e • n :=
  field_derivative_triangular hF χ hχ v w x hFx hgx hvx hw n T hn hT a b e ha hb he

/-- Item `A/planar_geometry/disp/009` (`paper/appendices/planar_geometry.tex:115-117`), in the
proof of Lemma `art:planar-field`: "with bounded coefficients". Under the assumptions of the
lemma, if $w$ is locally Lipschitz on an open $N$ containing the compact buffer $Q$ ("Smaller
compact buffers give uniform field and derivative bounds", line 98), there is one bound $B$
for the coefficients $a=T^TDwT$, $b=T^TDw\,n$, $e=n^TDw\,n$ at every $x\in Q$ and every unit
normal $n$ with $T$ its rotation. -/
theorem derivative_coefficients_bounded (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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

/-! ### Transversality of eligible steps -/

/-- Item `A/planar_geometry/disp/010` (`paper/appendices/planar_geometry.tex:134-137`), in the
proof of Lemma `art:planar-field`:
\[ d/\norm{s}\longrightarrow-\bar g^T\hat s>0,\qquad
   t/\norm{s}\longrightarrow(\bar h-\bar g)^T\hat s=0. \]
Under the assumptions of the lemma and the facts proved before (visibility $\eta>0$ and common
pairing of $w$ on $Q$): pairs $x_k,z_k$ with gradients $g_k,h_k$ coalesce to $p\in Q$
($s_k=z_k-x_k\to0$, $x_k\to p$), $s_k/\norm{s_k}\to\hat s$, $g_k\to\bar g$, $h_k\to\bar h$ with
$\bar g,\bar h\in\partial F(p)$, and $\hat s=-w(p)/\norm{w(p)}$ ("Hence"); $d_k=-g_k^Ts_k$,
$t_k=(h_k-g_k)^Ts_k$. Gradient limits are written `gbar`, `hbar`, the limit direction `shat`.

The display is a step of a proof by contradiction: in the TeX the pairs are eligible, and with
eligibility these assumptions are contradictory by design (`transversality_contradiction`
derives `False` from them, which is the next sentence of the proof). The theorem is therefore
stated without eligibility, which the display does not need; its assumptions are then
satisfiable, as the `example` at the end of this module shows (constant sequences at a smooth
point of the objective of Theorem `art:nonradial-example`). -/
theorem transversality_limits (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (shat gbar hbar : Vec 2) (hshat : Tendsto (fun k => normalized (z k - x k)) atTop (𝓝 shat))
    (hgbar : Tendsto g atTop (𝓝 gbar)) (hhbar : Tendsto h atTop (𝓝 hbar))
    (hgmem : gbar ∈ subdifferential F p) (hhmem : hbar ∈ subdifferential F p)
    (hshat_eq : shat = -normalized (w p))
    (d t : ℕ → ℝ) (hd : ∀ k, d k = -dot (g k) (z k - x k))
    (ht : ∀ k, t k = dot (h k - g k) (z k - x k)) :
    Tendsto (fun k => d k / ‖euclideanVector (z k - x k)‖) atTop (𝓝 (-dot gbar shat)) ∧
      0 < -dot gbar shat ∧
      Tendsto (fun k => t k / ‖euclideanVector (z k - x k)‖) atTop (𝓝 (dot (hbar - gbar) shat)) ∧
      dot (hbar - gbar) shat = 0 := by
  have hdk : (fun k => d k / ‖euclideanVector (z k - x k)‖) =
      fun k => -dot (g k) (normalized (z k - x k)) := by
    funext k
    rw [hd k, dot_normalized_right, neg_div]
  have htk : (fun k => t k / ‖euclideanVector (z k - x k)‖) =
      fun k => dot (h k - g k) (normalized (z k - x k)) := by
    funext k
    rw [ht k, dot_normalized_right]
  have hwp : 0 < dot gbar (w p) := hη.trans_le (hvis p hpQ gbar hgmem)
  have hw0 : w p ≠ 0 := by
    intro h0
    rw [h0] at hwp
    simp [dot] at hwp
  have hwn : 0 < ‖euclideanVector (w p)‖ := norm_pos_iff.mpr (by
    intro he
    exact hw0 (congrArg (fun y : EuclideanSpace ℝ (Fin 2) => fun i => y i) he))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdk]
    exact ((continuous_dot.tendsto _).comp (hgbar.prodMk_nhds hshat)).neg
  · rw [hshat_eq, dot_neg_right_vec, neg_neg, dot_normalized_right]
    exact div_pos hwp hwn
  · rw [htk]
    exact (continuous_dot.tendsto _).comp ((hhbar.sub hgbar).prodMk_nhds hshat)
  · rw [hshat_eq, dot_neg_right_vec, dot_normalized_right, dot_sub_left,
      hcommon p hpQ hbar hhmem gbar hgmem, sub_self, zero_div, neg_zero]

/-- Proof of Lemma `art:planar-field`, undisplayed claim of
`paper/appendices/planar_geometry.tex:138-139` (not a register item): the limits of display
`disp/010` contradict $t\ge(1-c_2)d$. Under the assumptions of `transversality_limits`, if
the pairs are eligible, then `False`. (The uniform transversality of item 2 of the lemma, which
this contradiction proves, is the library's `PlanarAllPairs.compact_pair_transversality_length`.) -/
theorem transversality_contradiction (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (w : Vec 2 → Vec 2) (Q : Set (Vec 2)) (η : ℝ) (hη : 0 < η)
    (hvis : ∀ p ∈ Q, ∀ a ∈ subdifferential F p, η ≤ dot a (w p))
    (hcommon : ∀ p ∈ Q, ∀ a ∈ subdifferential F p, ∀ b ∈ subdifferential F p,
      dot a (w p) = dot b (w p))
    (x z g h : ℕ → Vec 2) (hpair : ∀ k, EligiblePair F c₁ c₂ (x k) (z k) (g k) (h k))
    (p : Vec 2) (hpQ : p ∈ Q)
    (shat gbar hbar : Vec 2) (hshat : Tendsto (fun k => normalized (z k - x k)) atTop (𝓝 shat))
    (hgbar : Tendsto g atTop (𝓝 gbar)) (hhbar : Tendsto h atTop (𝓝 hbar))
    (hgmem : gbar ∈ subdifferential F p) (hhmem : hbar ∈ subdifferential F p)
    (hshat_eq : shat = -normalized (w p)) : False := by
  have hwp : 0 < dot gbar (w p) := hη.trans_le (hvis p hpQ gbar hgmem)
  have hw0 : w p ≠ 0 := by
    intro h0
    rw [h0] at hwp
    simp [dot] at hwp
  have hwn : 0 < ‖euclideanVector (w p)‖ := norm_pos_iff.mpr (by
    intro he
    exact hw0 (congrArg (fun y : EuclideanSpace ℝ (Fin 2) => fun i => y i) he))
  have hlim1 : Tendsto (fun k => -dot (g k) (normalized (z k - x k))) atTop
      (𝓝 (-dot gbar shat)) :=
    ((continuous_dot.tendsto _).comp (hgbar.prodMk_nhds hshat)).neg
  have hlim2 : Tendsto (fun k => dot (h k - g k) (normalized (z k - x k))) atTop
      (𝓝 (dot (hbar - gbar) shat)) :=
    (continuous_dot.tendsto _).comp ((hhbar.sub hgbar).prodMk_nhds hshat)
  have hpos : 0 < -dot gbar shat := by
    rw [hshat_eq, dot_neg_right_vec, neg_neg, dot_normalized_right]
    exact div_pos hwp hwn
  have hzero : dot (hbar - gbar) shat = 0 := by
    rw [hshat_eq, dot_neg_right_vec, dot_normalized_right, dot_sub_left,
      hcommon p hpQ hbar hhmem gbar hgmem, sub_self, zero_div, neg_zero]
  have hineq : ∀ k, (1 - c₂) * (-dot (g k) (normalized (z k - x k))) ≤
      dot (h k - g k) (normalized (z k - x k)) := fun k =>
    PlanarAllPairs.eligible_normalized_wolfe (hpair k)
  have hle := le_of_tendsto_of_tendsto (hlim1.const_mul (1 - c₂)) hlim2
    (Eventually.of_forall hineq)
  rw [hzero] at hle
  have : 0 < (1 - c₂) * -dot gbar shat := mul_pos (sub_pos.mpr hc₂) hpos
  linarith

/-! ### Transport charged to decrease -/

/-- Item `A/planar_geometry/disp/011` (`paper/appendices/planar_geometry.tex:149-151`), equation
`art:planar-determinant-derivative`, in the proof of Lemma `art:planar-field`:
"At a smooth point the basis $(T,n)$ has determinant $-1$. Writing $s=s_TT+s_nn$, direct
calculation yields
\[ \det(s,Dw\,s)=s_n\bigl[(a-e)s_T+bs_n\bigr]." \]
Under the assumptions of the lemma, for an eligible pair $x,z$ with step $s=z-x$ and a segment
point $q=x+\theta s$ at which $F$ is $C^2$ with $\nabla F(q)\ne0$ and $w$ is given by
(`art:planar-field-formula`) near $q$, with $n,T,a,b,e$ as in `derivative_triangular` at $q$ and
$s_T=T^Ts$, $s_n=n^Ts$. -/
theorem determinant_derivative (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (hw : ∀ᶠ y in 𝓝 q, ∀ φ, normal φ = normalized (coordinateGradient F y) →
        w y = fieldFormula (fun j ψ => χ j (normal ψ)) v (F y) φ)
    (n T : Vec 2) (hn : n = normalized (coordinateGradient F q))
    (hT : T = PlanarAmbientFrame.rotate n) (a b e : ℝ) (ha : a = dot T (fderiv ℝ w q T))
    (hb : b = dot T (fderiv ℝ w q n)) (he : e = dot n (fderiv ℝ w q n))
    (sT sn : ℝ) (hsT : sT = dot T s) (hsn : sn = dot n s) :
    pairDet T n = -1 ∧ s = sT • T + sn • n ∧
      pairDet s (fderiv ℝ w q s) = sn * ((a - e) * sT + b * sn) := by
  obtain ⟨-, htan, -, -⟩ :=
    field_derivative_triangular hF χ hχ v w q hFq hgq hvq hw n T hn hT a b e ha hb he
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

/-- Item `A/planar_geometry/disp/012` (`paper/appendices/planar_geometry.tex:160-164`), in the
proof of Lemma `art:planar-field`: for $H(\theta)=\log|D(\theta)|$,
\[ |H'_+(\theta)|\le A|\varphi'_+(\theta)|\le A\bigl(\varphi'_+(\theta)+2d\bigr),
   \qquad 0\le\theta<1. \]
Under the assumptions of the lemma and the facts proved before: $w$ is the field of the proof
for smooth ambient cutoffs $\chi_j$ and velocities $v_j$, locally Lipschitz on an open
$N\supset Q$ ($Q$ compact); on $Q$ the velocities are $C^1$ at $F$, every point is smooth
($C^2$) or has $w=v_j\circ F$ nearby (`art:planar-corner-field`), and $g^Tw\ge\eta>0$ for all
subgradients; eligible pairs in $U$ with $\norm{s}<\delta$ have their segments in $Q$ and
$|D(\theta)|\ge\kappa\norm{s}$ (transversality). Then there is one constant $A\ge0$, chosen
before the pair, such that for every such pair, with $q(\theta)=x+\theta s$,
$\varphi(\theta)=F(q(\theta))$, $D(\theta)=\det(s,w(q(\theta)))$ and $d=-g^Ts$: $H$ has a right
derivative $H'_+(\theta)$ (`derivWithin H (Ioi θ) θ`, a `HasDerivWithinAt` on `Ici θ`) and the
display holds with $\varphi'_+(\theta)$ = `derivWithin φ (Ioi θ) θ`. -/
theorem log_determinant_derivative_bound (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ U, ∀ z ∈ U, ∀ g h : Vec 2, EligiblePair F c₁ c₂ x z g h →
      ‖euclideanVector (z - x)‖ < δ →
      ∀ (s : Vec 2) (d : ℝ) (q : ℝ → Vec 2) (φ D H : ℝ → ℝ), s = z - x → d = -dot g s →
        q = (fun θ => x + θ • s) → φ = (fun θ => F (q θ)) →
        D = (fun θ => pairDet s (w (q θ))) → H = (fun θ => Real.log |D θ|) →
        ∀ θ ∈ Ico (0 : ℝ) 1,
          HasDerivWithinAt H (derivWithin H (Ioi θ) θ) (Ici θ) θ ∧
          |derivWithin H (Ioi θ) θ| ≤ A * |derivWithin φ (Ioi θ) θ| ∧
          A * |derivWithin φ (Ioi θ) θ| ≤ A * (derivWithin φ (Ioi θ) θ + 2 * d) := by
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
  intro x hx z hz g h hp hs s d q φ D H hs_eq hd_eq hq_eq hφ_eq hD_eq hH_eq θ hθ
  subst hs_eq hq_eq hφ_eq hD_eq hH_eq
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
  have hsn : 0 < ‖euclideanVector (z - x)‖ := norm_pos_iff.mpr (by
    intro he
    exact hs0 (congrArg (fun y : EuclideanSpace ℝ (Fin 2) => fun i => y i) he))
  have hDθ : pairDet (z - x) (PlanarObjectiveField.field hF χ v (x + θ • (z - x))) ≠ 0 := by
    intro he
    rw [he, abs_zero] at htr
    linarith [mul_pos hκ hsn]
  have hH' : HasDerivWithinAt
      (fun τ : ℝ =>
        Real.log |pairDet (z - x) (PlanarObjectiveField.field hF χ v (x + τ • (z - x)))|)
      (D' / pairDet (z - x) (PlanarObjectiveField.field hF χ v (x + θ • (z - x)))) (Ici θ) θ := by
    simpa only [Real.log_abs] using hD'.log hDθ
  have hderivH := hH'.Ioi_of_Ici.derivWithin (uniqueDiffWithinAt_Ioi θ)
  have h0 : HasDerivAt (fun τ : ℝ => F (x + τ • (z - x))) (-d) 0 := by
    have hl : HasDerivAt (fun τ : ℝ => x + τ • (z - x)) (z - x) 0 := by
      simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (z - x)).const_add x
    have hcomp := hp.gradient_x.comp_hasDerivAt_of_eq 0 hl (by simp)
    simpa only [gradientFunctional_apply, hd_eq, neg_neg] using hcomp
  have hlower := PlanarScalarTransport.convex_right_derivative_lower hφc h0 hθ.1
  have hd0 : 0 ≤ d := by
    rw [hd_eq]
    exact hp.decrease_pos.le
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hderivH] using hH'
  · simpa only [hderivH] using hbound
  · apply mul_le_mul_of_nonneg_left _ hA
    rw [abs_le]
    constructor <;> linarith

/-- Item `A/planar_geometry/disp/013` (`paper/appendices/planar_geometry.tex:175-178`), in the
proof of Lemma `art:planar-field`: "Apply this fact to both
\[ \pm\bigl(H(\theta)-H(0)\bigr)-A\bigl(\varphi(\theta)-\varphi(0)+2d\theta\bigr). \]
Both start at zero and have nonpositive right derivative."

Under the assumptions of the lemma, for an eligible pair with $s,d,q,\varphi,D,H$ as in
`log_determinant_derivative_bound`, $D$ continuous and nonzero on $[0,1]$ (transversality) and
$A\ge0$ satisfying the bound of display `disp/012` on $[0,1)$: for each sign $\sigma=\pm1$ the
displayed function $u$ has $u(0)=0$ and, on $[0,1)$, the right derivative
$\sigma H'_+-A(\varphi'_++2d)\le0$; applying the one-sided comparison gives $u(1)\le0$. -/
theorem comparison_functions (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (w : Vec 2 → Vec 2) (x z g h : Vec 2) (_hp : EligiblePair F c₁ c₂ x z g h)
    (s : Vec 2) (_hs : s = z - x) (d : ℝ) (_hd : d = -dot g s) (q : ℝ → Vec 2)
    (hq : q = fun θ => x + θ • s) (φ D H : ℝ → ℝ) (hφ : φ = fun θ => F (q θ))
    (_hD : D = fun θ => pairDet s (w (q θ))) (hH : H = fun θ => Real.log |D θ|)
    (hDcont : ContinuousOn D (Icc 0 1)) (hD0 : ∀ θ ∈ Icc (0 : ℝ) 1, D θ ≠ 0)
    (A : ℝ) (_hA : 0 ≤ A)
    (hbound : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt H (derivWithin H (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin H (Ioi θ) θ| ≤ A * |derivWithin φ (Ioi θ) θ| ∧
      A * |derivWithin φ (Ioi θ) θ| ≤ A * (derivWithin φ (Ioi θ) θ + 2 * d))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : ℝ → ℝ)
    (hu : u = fun θ => σ * (H θ - H 0) - A * (φ θ - φ 0 + 2 * d * θ)) :
    u 0 = 0 ∧
      (∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u
          (σ * derivWithin H (Ioi θ) θ - A * (derivWithin φ (Ioi θ) θ + 2 * d)) (Ici θ) θ ∧
        σ * derivWithin H (Ioi θ) θ - A * (derivWithin φ (Ioi θ) θ + 2 * d) ≤ 0) ∧
      u 1 ≤ 0 := by
  have hHcont : ContinuousOn H (Icc 0 1) := by
    rw [hH]
    simpa only [Real.log_abs] using hDcont.log hD0
  exact comparison_core hF x s d φ H (by rw [hφ, hq]) hHcont A hbound σ hσ u hu

/-- Item `A/planar_geometry/disp/014` (`paper/appendices/planar_geometry.tex:181-183`), in the
proof of Lemma `art:planar-field`: "Since $\varphi(1)\le\varphi(0)$,
\[ |H(1)-H(0)|\le2Ad." \]
Under the assumptions of `comparison_functions` (without the sign and $u$). -/
theorem log_determinant_increment (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (w : Vec 2 → Vec 2) (x z g h : Vec 2) (hp : EligiblePair F c₁ c₂ x z g h)
    (s : Vec 2) (hs : s = z - x) (d : ℝ) (_hd : d = -dot g s) (q : ℝ → Vec 2)
    (hq : q = fun θ => x + θ • s) (φ D H : ℝ → ℝ) (hφ : φ = fun θ => F (q θ))
    (_hD : D = fun θ => pairDet s (w (q θ))) (hH : H = fun θ => Real.log |D θ|)
    (hDcont : ContinuousOn D (Icc 0 1)) (hD0 : ∀ θ ∈ Icc (0 : ℝ) 1, D θ ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt H (derivWithin H (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin H (Ioi θ) θ| ≤ A * |derivWithin φ (Ioi θ) θ| ∧
      A * |derivWithin φ (Ioi θ) θ| ≤ A * (derivWithin φ (Ioi θ) θ + 2 * d)) :
    |H 1 - H 0| ≤ 2 * A * d := by
  have hHcont : ContinuousOn H (Icc 0 1) := by
    rw [hH]
    simpa only [Real.log_abs] using hDcont.log hD0
  have hdesc : φ 1 ≤ φ 0 := by
    have harm := hp.armijo
    have hc := mul_pos hc₁ hp.decrease_pos
    rw [hφ, hq, hs]
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel]
    linarith
  exact increment_core hF x s d φ H (by rw [hφ, hq]) hHcont hdesc A hA hbound

/-- Proof of Lemma `art:planar-field`, undisplayed claims of
`paper/appendices/planar_geometry.tex:184-189` (not a register item): "Set
$\lambda=D(1)/D(0)>0$. Because $s,w(x)$ are linearly independent, solving in that basis gives
$w(z)=\lambda w(x)+\beta s$; the preceding bound is $|\log\lambda|\le2Ad$. For $0<d\le1$,
convexity of the exponential on $[0,1]$ gives $\lambda^2\le\exp(4Ad)\le1+(\exp(4A)-1)d$."
Under the assumptions of `log_determinant_increment`. -/
theorem transport_constants (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (w : Vec 2 → Vec 2) (x z g h : Vec 2) (hp : EligiblePair F c₁ c₂ x z g h)
    (s : Vec 2) (hs : s = z - x) (d : ℝ) (hd : d = -dot g s) (q : ℝ → Vec 2)
    (hq : q = fun θ => x + θ • s) (φ D H : ℝ → ℝ) (hφ : φ = fun θ => F (q θ))
    (hD : D = fun θ => pairDet s (w (q θ))) (hH : H = fun θ => Real.log |D θ|)
    (hDcont : ContinuousOn D (Icc 0 1)) (hD0 : ∀ θ ∈ Icc (0 : ℝ) 1, D θ ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ θ ∈ Ico (0 : ℝ) 1, HasDerivWithinAt H (derivWithin H (Ioi θ) θ) (Ici θ) θ ∧
      |derivWithin H (Ioi θ) θ| ≤ A * |derivWithin φ (Ioi θ) θ| ∧
      A * |derivWithin φ (Ioi θ) θ| ≤ A * (derivWithin φ (Ioi θ) θ + 2 * d))
    (lam : ℝ) (hlam : lam = D 1 / D 0) :
    0 < lam ∧ (∃ β : ℝ, w z = lam • w x + β • s) ∧ |Real.log lam| ≤ 2 * A * d ∧
      (d ≤ 1 → lam ^ 2 ≤ Real.exp (4 * A * d) ∧
        Real.exp (4 * A * d) ≤ 1 + (Real.exp (4 * A) - 1) * d) := by
  have hHcont : ContinuousOn H (Icc 0 1) := by
    rw [hH]
    simpa only [Real.log_abs] using hDcont.log hD0
  have hdesc : φ 1 ≤ φ 0 := by
    have harm := hp.armijo
    have hc := mul_pos hc₁ hp.decrease_pos
    rw [hφ, hq, hs]
    simp only [one_smul, zero_smul, add_zero, add_sub_cancel]
    linarith
  have hinc := increment_core hF x s d φ H (by rw [hφ, hq]) hHcont hdesc A hA hbound
  have hlampos : 0 < lam := hlam ▸ PlanarScalarTransport.positive_endpoint_ratio hDcont hD0
  have hD00 := hD0 0 (by norm_num)
  have hD10 := hD0 1 (by norm_num)
  have hloglam : |Real.log lam| ≤ 2 * A * d := by
    rw [hlam, Real.log_div hD10 hD00]
    rw [hH] at hinc
    simpa only [Real.log_abs] using hinc
  have hd0 : 0 ≤ d := hd ▸ hs ▸ hp.decrease_pos.le
  refine ⟨hlampos, ?_, hloglam, ?_⟩
  · have hDx : D 0 = pairDet s (w x) := by rw [hD, hq]; simp
    have hDz : D 1 = pairDet s (w z) := by rw [hD, hq, hs]; simp
    refine ⟨pairDet (w z) (w x) / pairDet s (w x), ?_⟩
    rw [hlam, hDx, hDz]
    exact PlanarTransport.determinant_transport s (w x) (w z) (hDx ▸ hD00)
  · intro hd1
    have hlog' : 2 * Real.log lam ≤ 4 * A * d := by
      have hl := (le_abs_self (Real.log lam)).trans hloglam
      linarith
    have he : Real.exp (4 * A * d) ≤ (1 - d) * Real.exp 0 + d * Real.exp (4 * A) := by
      have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (4 * A))
        (sub_nonneg.mpr hd1) hd0 (by ring : (1 - d) + d = 1)
      simpa only [smul_eq_mul, mul_zero, zero_add, mul_comm d, mul_assoc] using h
    refine ⟨?_, ?_⟩
    · calc lam ^ 2 = Real.exp (2 * Real.log lam) := by
            rw [two_mul, Real.exp_add, Real.exp_log hlampos, pow_two]
        _ ≤ Real.exp (4 * A * d) := Real.exp_le_exp.mpr hlog'
    · calc Real.exp (4 * A * d) ≤ (1 - d) * Real.exp 0 + d * Real.exp (4 * A) := he
        _ = 1 + (Real.exp (4 * A) - 1) * d := by rw [Real.exp_zero]; ring

/-! ### The secant correction -/

/-- Item `A/planar_geometry/disp/015` (`paper/appendices/planar_geometry.tex:196-199`), in the
proof of Lemma `art:planar-field`: "First suppose the endpoints use the same smooth branch $f$.
On a larger convex chart, with Lipschitz constant $M>0$, sufficiently close buffered endpoints
satisfy
\[ \norm{\nabla f(z)-\nabla f(x)}^2\le2M\bigl[f(z)-f(x)-\nabla f(x)^T(z-x)\bigr]." \]
Under the assumptions of the lemma: $f$ is convex and $C^2$ on the open convex chart $V$, with
$\nabla f$ $M$-Lipschitz on $V$ in the Euclidean norm; the buffer $B$ has its $\rho$-balls in
$V$; the eligible pair $x,z\in B$ uses the branch $f$ at both endpoints and
$\norm{z-x}<\rho$. -/
theorem branch_cocoercivity (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (f : Vec 2 → ℝ) (V : Set (Vec 2)) (hVopen : IsOpen V) (hfconv : ConvexOn ℝ V f)
    (hfC : ContDiffOn ℝ 2 f V) (M : ℝ) (hM : 0 < M)
    (hLip : ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient f u -
      coordinateGradient f u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (B : Set (Vec 2)) (ρ : ℝ) (hρ : 0 < ρ)
    (hBV : ∀ u ∈ B, ∀ u' : Vec 2, ‖euclideanVector (u' - u)‖ < ρ → u' ∈ V)
    (x z g h : Vec 2) (_hp : EligiblePair F c₁ c₂ x z g h) (_hfx : f x = F x)
    (_hfz : f z = F z) (hx : x ∈ B) (hz : z ∈ B) (hxz : ‖euclideanVector (z - x)‖ < ρ) :
    sqNorm (coordinateGradient f z - coordinateGradient f x) ≤
      2 * M * (f z - f x - dot (coordinateGradient f x) (z - x)) :=
  cocoercivity_core f V hVopen hfconv hfC M hM hLip B ρ hρ hBV x z hx hz hxz

/-- Proof of Lemma `art:planar-field`, undisplayed claims of
`paper/appendices/planar_geometry.tex:206-208` (not a register item): "Since the branch values
and gradients at both endpoints agree with those of $F$, the bracket is at most $t$.
Boundedness of $w$ then bounds $(y^Tw(z))^2/t$ uniformly." Under the assumptions of
`branch_cocoercivity`, with $\nabla f(x)=g$, $\nabla f(z)=h$ and $\norm{w(z)}\le G$: the bracket
is at most $t=(h-g)^T(z-x)$ and $(y^Tw(z))^2/t\le2MG^2$. -/
theorem same_branch_secant (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (f : Vec 2 → ℝ) (V : Set (Vec 2)) (hVopen : IsOpen V) (hfconv : ConvexOn ℝ V f)
    (hfC : ContDiffOn ℝ 2 f V) (M : ℝ) (hM : 0 < M)
    (hLip : ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient f u -
      coordinateGradient f u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (B : Set (Vec 2)) (ρ : ℝ) (hρ : 0 < ρ)
    (hBV : ∀ u ∈ B, ∀ u' : Vec 2, ‖euclideanVector (u' - u)‖ < ρ → u' ∈ V)
    (x z g h : Vec 2) (hp : EligiblePair F c₁ c₂ x z g h) (hfx : f x = F x) (hfz : f z = F z)
    (hgx : coordinateGradient f x = g) (hhz : coordinateGradient f z = h)
    (hx : x ∈ B) (hz : z ∈ B) (hxz : ‖euclideanVector (z - x)‖ < ρ)
    (w : Vec 2 → Vec 2) (G : ℝ) (hwz : ‖euclideanVector (w z)‖ ≤ G) :
    f z - f x - dot (coordinateGradient f x) (z - x) ≤ dot (h - g) (z - x) ∧
      (dot (h - g) (w z)) ^ 2 / dot (h - g) (z - x) ≤ 2 * M * G ^ 2 := by
  have hcoco := cocoercivity_core f V hVopen hfconv hfC M hM hLip B ρ hρ hBV x z hx hz hxz
  have hsupp := convex_supporting_inequality hF hp.gradient_z x
  have hbracket : f z - f x - dot (coordinateGradient f x) (z - x) ≤ dot (h - g) (z - x) := by
    rw [hfx, hfz, hgx, dot_sub_left]
    have hxz' : dot h (x - z) = -dot h (z - x) := by
      rw [show x - z = -(z - x) by abel, dot_neg_right_vec]
    linarith
  refine ⟨hbracket, ?_⟩
  have hd0 : 0 < -dot g (z - x) := hp.decrease_pos
  have ht0 : 0 < dot (h - g) (z - x) := by
    have hc := hp.curvature
    change (1 - c₂) * (-dot g (z - x)) ≤ dot (h - g) (z - x) at hc
    nlinarith [sub_pos.mpr hc₂]
  have hG : 0 ≤ G := (norm_nonneg _).trans hwz
  have hw2 : sqNorm (w z) ≤ G ^ 2 := by
    rw [← euclidean_norm_sq_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) hwz 2
  rw [hgx, hhz] at hcoco
  rw [div_le_iff₀ ht0]
  calc (dot (h - g) (w z)) ^ 2 ≤ sqNorm (h - g) * sqNorm (w z) :=
        dot_sq_le_sqNorm_mul_sqNorm _ _
    _ ≤ (2 * M * dot (h - g) (z - x)) * G ^ 2 := by
        apply mul_le_mul _ hw2 (sqNorm_nonneg _) (by positivity)
        have hb' : f z - f x - dot g (z - x) ≤ dot (h - g) (z - x) := by
          simpa only [hgx] using hbracket
        nlinarith
    _ = 2 * M * G ^ 2 * dot (h - g) (z - x) := by ring

/-- Proof of Lemma `art:planar-field`, undisplayed claims of
`paper/appendices/planar_geometry.tex:210-212` (not a register item): "For different endpoint
branches $i,j$ in a two-branch chart, the segment contains a tie point $p$. There
$(\nabla f_j(p)-\nabla f_i(p))^Tw(p)=0$." Under the assumptions of the lemma: $F=\max(f_0,f_1)$
on the open convex chart $V$ with convex $C^2$ branches, $w$ has the common pairing on $V$,
and the eligible pair $x,z\in V$ uses branch $i$ at $x$ and branch $j\ne i$ at $z$. -/
theorem crossing_tie_point (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (hmax : ∀ u ∈ V, F u = max (f 0 u) (f 1 u)) (w : Vec 2 → Vec 2)
    (hcommon : ∀ p ∈ V, ∀ a ∈ subdifferential F p, ∀ b ∈ subdifferential F p,
      dot a (w p) = dot b (w p))
    (x z g h : Vec 2) (hx : x ∈ V) (hz : z ∈ V) (_hp : EligiblePair F c₁ c₂ x z g h)
    (i j : Fin 2) (hij : i ≠ j) (hi : f i x = F x) (hj : f j z = F z) :
    ∃ p ∈ segment ℝ x z, f i p = F p ∧ f j p = F p ∧
      dot (coordinateGradient (f j) p - coordinateGradient (f i) p) (w p) = 0 :=
  tie_point_core hF f V hVconv hVopen hfC (fun u hu => isGreatest_of_max f (hmax u hu)) w hcommon
    x z hx hz i j hij hi hj

/-- Item `A/planar_geometry/disp/016` (`paper/appendices/planar_geometry.tex:214-216`), in the
proof of Lemma `art:planar-field`: "The branch gradients and $w$ are Lipschitz, so
\[ |y^Tw(z)|\le A_1\norm{s}." \]
Under the assumptions of the lemma: $F=\max(f_0,f_1)$ on the open convex chart $V$ with convex
$C^2$ branches whose gradients are $M$-Lipschitz and bounded by $H_b$ on $V$; $w$ is
$B_w$-Lipschitz, bounded by $G$ and has the common pairing on $V$ (Euclidean norms). Then one
constant $A_1\ge0$ works for every eligible pair $x,z\in V$ that uses branch $i$ at $x$ and a
different branch $j$ at $z$ ($y=h-g$, $s=z-x$). -/
theorem crossing_numerator (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (hmax : ∀ u ∈ V, F u = max (f 0 u) (f 1 u)) (M : ℝ) (hM : 0 < M)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (Hb : ℝ) (hgradB : ∀ i, ∀ u ∈ V, ‖euclideanVector (coordinateGradient (f i) u)‖ ≤ Hb)
    (w : Vec 2 → Vec 2) (Bw G : ℝ)
    (hwLip : ∀ u ∈ V, ∀ u' ∈ V,
      ‖euclideanVector (w u - w u')‖ ≤ Bw * ‖euclideanVector (u - u')‖)
    (hwB : ∀ u ∈ V, ‖euclideanVector (w u)‖ ≤ G)
    (hcommon : ∀ p ∈ V, ∀ a ∈ subdifferential F p, ∀ b ∈ subdifferential F p,
      dot a (w p) = dot b (w p)) :
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ x z g h : Vec 2, x ∈ V → z ∈ V → EligiblePair F c₁ c₂ x z g h →
      ∀ i j : Fin 2, i ≠ j → f i x = F x → f j z = F z →
        |dot (h - g) (w z)| ≤ A₁ * ‖euclideanVector (z - x)‖ := by
  by_cases hV : V.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hV
    have hHb : 0 ≤ Hb := (norm_nonneg _).trans (hgradB 0 u₀ hu₀)
    have hG : 0 ≤ G := (norm_nonneg _).trans (hwB u₀ hu₀)
    set Bw' := max Bw 0
    have hwLip' : ∀ u ∈ V, ∀ u' ∈ V,
        ‖euclideanVector (w u - w u')‖ ≤ Bw' * ‖euclideanVector (u - u')‖ := fun u hu u' hu' =>
      (hwLip u hu u' hu').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    refine ⟨2 * M * G + 2 * Hb * Bw', by positivity, ?_⟩
    intro x z g h hx hz hp i j hij hi hj
    exact crossing_core hF f V hVconv hVopen hfC (fun u hu => isGreatest_of_max f (hmax u hu))
      M Hb hM.le hHb hLip hgradB w Bw' G
      (le_max_right _ _) hG hwLip' hwB hcommon x z g h hx hz hp.gradient_x hp.gradient_z i j hij
      hi hj
  · refine ⟨0, le_rfl, ?_⟩
    intro x _ _ _ hx
    exact absurd ⟨x, hx⟩ hV

/-- Item `A/planar_geometry/disp/017` (`paper/appendices/planar_geometry.tex:219-221`), in the
proof of Lemma `art:planar-field`: "Put $r=\nabla f_j(z)-\nabla f_j(x)$, so
$\norm{r}\le M\norm{s}$. Then
\[ \nabla f_i(x)^Ts=-d,\qquad \nabla f_j(x)^Ts=t-d-r^Ts." \]
Under the assumptions of `crossing_numerator` (chart and pair), with $s=z-x$, $y=h-g$,
$d=-g^Ts$, $t=y^Ts$. -/
theorem crossing_pairings (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (hmax : ∀ u ∈ V, F u = max (f 0 u) (f 1 u)) (M : ℝ) (_hM : 0 < M)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (x z g h : Vec 2) (hx : x ∈ V) (hz : z ∈ V) (hp : EligiblePair F c₁ c₂ x z g h)
    (i j : Fin 2) (_hij : i ≠ j) (hi : f i x = F x) (hj : f j z = F z)
    (s y : Vec 2) (hs : s = z - x) (hy : y = h - g) (d t : ℝ) (hd : d = -dot g s)
    (ht : t = dot y s) (r : Vec 2)
    (hr : r = coordinateGradient (f j) z - coordinateGradient (f j) x) :
    ‖euclideanVector r‖ ≤ M * ‖euclideanVector s‖ ∧
      dot (coordinateGradient (f i) x) s = -d ∧
      dot (coordinateGradient (f j) x) s = t - d - dot r s :=
  crossing_pairings_core hF f V hVopen hfC (fun u hu => isGreatest_of_max f (hmax u hu)) M hLip
    x z g h hx hz hp.gradient_x hp.gradient_z
    i j hi hj s y hs hy d t hd ht r hr

/-- Item `A/planar_geometry/disp/018` (`paper/appendices/planar_geometry.tex:224-227`), in the
proof of Lemma `art:planar-field`: "The two gradient rows are uniformly independent on the
smaller chart. Their inverse bound and eligibility imply
\[ \norm{s}\le A_2(2d+t+M\norm{s}^2)\le A_2\Bigl(1+\frac{2}{1-c_2}\Bigr)t+A_2M\norm{s}^2." \]
Under the assumptions of `crossing_pairings`, with the inverse bound
$\norm{u}\le A_2(|\nabla f_0(x')^Tu|+|\nabla f_1(x')^Tu|)$ for all $u$ and $x'\in V$. -/
theorem crossing_step_bound (F : Vec 2 → ℝ) (hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (hmax : ∀ u ∈ V, F u = max (f 0 u) (f 1 u)) (M : ℝ) (_hM : 0 < M)
    (hLip : ∀ i, ∀ u ∈ V, ∀ u' ∈ V, ‖euclideanVector (coordinateGradient (f i) u -
      coordinateGradient (f i) u')‖ ≤ M * ‖euclideanVector (u - u')‖)
    (A₂ : ℝ) (hA₂ : 0 ≤ A₂)
    (hrows : ∀ u ∈ V, ∀ v : Vec 2, ‖euclideanVector v‖ ≤
      A₂ * (|dot (coordinateGradient (f 0) u) v| + |dot (coordinateGradient (f 1) u) v|))
    (x z g h : Vec 2) (hx : x ∈ V) (hz : z ∈ V) (hp : EligiblePair F c₁ c₂ x z g h)
    (i j : Fin 2) (hij : i ≠ j) (hi : f i x = F x) (hj : f j z = F z)
    (s y : Vec 2) (hs : s = z - x) (hy : y = h - g) (d t : ℝ) (hd : d = -dot g s)
    (ht : t = dot y s) (r : Vec 2)
    (hr : r = coordinateGradient (f j) z - coordinateGradient (f j) x) :
    ‖euclideanVector s‖ ≤ A₂ * (2 * d + t + M * ‖euclideanVector s‖ ^ 2) ∧
      A₂ * (2 * d + t + M * ‖euclideanVector s‖ ^ 2) ≤
        A₂ * (1 + 2 / (1 - c₂)) * t + A₂ * M * ‖euclideanVector s‖ ^ 2 := by
  obtain ⟨hrM, hia, hjb⟩ := crossing_pairings_core hF f V hVopen hfC
    (fun u hu => isGreatest_of_max f (hmax u hu)) M hLip x z g h hx hz
    hp.gradient_x hp.gradient_z i j hi hj s y hs hy d t hd ht r hr
  have hd0 : 0 ≤ d := by rw [hd, hs]; exact hp.decrease_pos.le
  have hσ : 0 < 1 - c₂ := sub_pos.mpr hc₂
  have hwolfe : (1 - c₂) * d ≤ t := by
    rw [hd, ht, hs, hy]
    exact hp.curvature
  have ht0 : 0 ≤ t := le_trans (mul_nonneg hσ.le hd0) hwolfe
  have hrows' : ‖euclideanVector s‖ ≤ A₂ * (|dot (coordinateGradient (f i) x) s| +
      |dot (coordinateGradient (f j) x) s|) := by
    have h0 := hrows x hx s
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using h0
    · simpa [add_comm] using h0
    · exact absurd rfl hij
  have hrs : |dot r s| ≤ M * ‖euclideanVector s‖ ^ 2 := by
    calc |dot r s| ≤ ‖euclideanVector r‖ * ‖euclideanVector s‖ :=
          PlanarCrossing.abs_dot_le_euclidean_norm r s
      _ ≤ M * ‖euclideanVector s‖ * ‖euclideanVector s‖ :=
          mul_le_mul_of_nonneg_right hrM (norm_nonneg _)
      _ = M * ‖euclideanVector s‖ ^ 2 := by ring
  have hb : |dot (coordinateGradient (f j) x) s| ≤ t + d + M * ‖euclideanVector s‖ ^ 2 := by
    rw [hjb]
    calc |t - d - dot r s| ≤ |t - d| + |dot r s| := abs_sub _ _
      _ ≤ (|t| + |d|) + |dot r s| := by gcongr; exact abs_sub _ _
      _ ≤ t + d + M * ‖euclideanVector s‖ ^ 2 := by
          rw [abs_of_nonneg ht0, abs_of_nonneg hd0]; gcongr
  refine ⟨?_, ?_⟩
  · calc ‖euclideanVector s‖ ≤ A₂ * (|dot (coordinateGradient (f i) x) s| +
          |dot (coordinateGradient (f j) x) s|) := hrows'
      _ ≤ A₂ * (d + (t + d + M * ‖euclideanVector s‖ ^ 2)) := by
          rw [hia, abs_neg, abs_of_nonneg hd0]
          gcongr
      _ = A₂ * (2 * d + t + M * ‖euclideanVector s‖ ^ 2) := by ring
  · have hdt : d ≤ t / (1 - c₂) := (le_div_iff₀ hσ).mpr (by linarith)
    have h2 : 2 * d + t ≤ (1 + 2 / (1 - c₂)) * t := by
      have : 2 * (t / (1 - c₂)) = 2 / (1 - c₂) * t := by ring
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hA₂]

/-- Proof of Lemma `art:planar-field`, undisplayed claims of
`paper/appendices/planar_geometry.tex:228-230` (not a register item): "For sufficiently small
$\norm{s}$, absorb the last term to obtain $t\ge a_0\norm{s}$ with $a_0>0$. Consequently
$(y^Tw(z))^2/t\le A_1^2\norm{s}/a_0$, uniformly bounded." Under the assumptions of the lemma,
for an eligible pair with the bounds of displays `disp/016` and `disp/018`, $A_2>0$ and
$A_2M\norm{s}\le1/2$, with $a_0=1/(2A_2(1+2/(1-c_2)))$. -/
theorem crossing_secant (F : Vec 2 → ℝ) (_hF : ConvexOn ℝ univ F) (Fstar : ℝ)
    (_hFstar : IsLeast (range F) Fstar) (C : Set (Vec 2)) (ℓ : ℝ) (_hCne : C.Nonempty)
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
    (w : Vec 2 → Vec 2) (x z g h : Vec 2) (hp : EligiblePair F c₁ c₂ x z g h)
    (s y : Vec 2) (hs : s = z - x) (hy : y = h - g) (d t : ℝ) (hd : d = -dot g s)
    (ht : t = dot y s) (M A₁ A₂ : ℝ) (_hM : 0 < M) (hA₁ : 0 ≤ A₁) (hA₂ : 0 < A₂)
    (hnum : |dot y (w z)| ≤ A₁ * ‖euclideanVector s‖)
    (hstep : ‖euclideanVector s‖ ≤
      A₂ * (1 + 2 / (1 - c₂)) * t + A₂ * M * ‖euclideanVector s‖ ^ 2)
    (hsmall : A₂ * M * ‖euclideanVector s‖ ≤ 1 / 2) (a₀ : ℝ)
    (ha₀ : a₀ = 1 / (2 * A₂ * (1 + 2 / (1 - c₂)))) :
    0 < a₀ ∧ a₀ * ‖euclideanVector s‖ ≤ t ∧
      (dot y (w z)) ^ 2 / t ≤ A₁ ^ 2 * ‖euclideanVector s‖ / a₀ := by
  have hσ : 0 < 1 - c₂ := sub_pos.mpr hc₂
  have hK : 0 < 1 + 2 / (1 - c₂) := by positivity
  have ha₀pos : 0 < a₀ := by rw [ha₀]; positivity
  have hsn := norm_nonneg (euclideanVector s)
  have hd0 : 0 < d := by rw [hd, hs]; exact hp.decrease_pos
  have htpos : 0 < t := by
    have hc := hp.curvature
    have : (1 - c₂) * d ≤ t := by rw [ht, hy, hd, hs]; exact hc
    nlinarith
  have hquad : A₂ * M * ‖euclideanVector s‖ ^ 2 ≤ ‖euclideanVector s‖ / 2 := by
    have := mul_le_mul_of_nonneg_right hsmall hsn
    nlinarith
  have hlin : ‖euclideanVector s‖ ≤ 2 * A₂ * (1 + 2 / (1 - c₂)) * t := by nlinarith
  have hlow : a₀ * ‖euclideanVector s‖ ≤ t := by
    rw [ha₀, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  refine ⟨ha₀pos, hlow, ?_⟩
  have hcorr := PlanarCrossing.crossing_secant_correction hA₁ (by positivity : 0 ≤ 1 / a₀) hsn
    htpos hnum (by rw [one_div_mul_eq_div, le_div_iff₀ ha₀pos]; linarith)
  calc (dot y (w z)) ^ 2 / t ≤ A₁ ^ 2 * (1 / a₀) * ‖euclideanVector s‖ := hcorr
    _ = A₁ ^ 2 * ‖euclideanVector s‖ / a₀ := by ring

/-! ### Non-vacuity

The witnesses below use the objective $F=\max\{f_0,f_1,f_2\}$ of Theorem `art:nonradial-example`
(`PlanarQuadraticExample.objective`, with branches `branch 0`, `branch 1`, `branch 2`), its
minimum $F_*=0$, the point $p_0=(40/721,39/721)$ (`pTie`), where $f_0=f_1>f_2$, the compact
set $C=\{p_0\}$ and the level $\ell=F(p_0)$. Each `example` applies theorems of this file to
explicit data, so Lean checks that all of their hypotheses hold together. -/

section NonVacuity

open BfgsVerification.PlanarQuadraticExample

/-- $\norm{a}\le c\norm{b}$ from $\norm{a}^2\le c^2\norm{b}^2$ (Euclidean norms). -/
theorem euclid_le_mul_of_sqNorm_le {a b : Vec 2} {c : ℝ} (hc : 0 ≤ c)
    (h : sqNorm a ≤ c ^ 2 * sqNorm b) : ‖euclideanVector a‖ ≤ c * ‖euclideanVector b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, euclidean_norm_sq_eq, euclidean_norm_sq_eq]
  exact h

/-- $\norm{a}\le c$ from $\norm{a}^2\le c^2$ (Euclidean norm). -/
theorem euclid_le_of_sqNorm_le {a : Vec 2} {c : ℝ} (hc : 0 ≤ c) (h : sqNorm a ≤ c ^ 2) :
    ‖euclideanVector a‖ ≤ c := by
  apply (sq_le_sq₀ (norm_nonneg _) hc).mp
  rw [euclidean_norm_sq_eq]
  exact h

/-- A Euclidean unit vector is its own normalization. -/
theorem normalized_of_sqNorm_eq_one {u : Vec 2} (hu : sqNorm u = 1) : normalized u = u := by
  have hn : ‖euclideanVector u‖ = 1 := by
    have h := euclidean_norm_sq_eq u
    rw [hu] at h
    nlinarith [norm_nonneg (euclideanVector u)]
  rw [normalized, hn, inv_one, one_smul]

/-- Normalization ignores positive factors. -/
theorem normalized_smul_of_pos {c : ℝ} (hc : 0 < c) (u : Vec 2) :
    normalized (c • u) = normalized u := by
  rw [normalized, normalized, euclideanVector_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
    smul_smul, mul_inv, mul_assoc, mul_comm (‖euclideanVector u‖⁻¹) c, ← mul_assoc,
    inv_mul_cancel₀ hc.ne', one_mul]

/-- The tie point $p_0=(40/721,39/721)$ of the objective of Theorem `art:nonradial-example`. -/
def pTie : Vec 2 := ![40 / 721, 39 / 721]

/-- $f_0(p_0)=f_1(p_0)>f_2(p_0)$. -/
theorem pTie_tie : branch 0 pTie = branch 1 pTie ∧ branch 2 pTie < branch 0 pTie := by
  simp only [pTie, branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The two-branch chart $V_0$ of the witnesses: the sup-norm ball of radius $1/100$ about
$p_0$. -/
def chartTie : Set (Vec 2) := Metric.ball pTie (1 / 100)

/-- $p_0\in V_0$. -/
theorem pTie_mem : pTie ∈ chartTie := Metric.mem_ball_self (by norm_num)

/-- Coordinates in $V_0$: $1/25<y_0,y_1<7/100$. -/
theorem chartTie_bounds {y : Vec 2} (hy : y ∈ chartTie) :
    1 / 25 < y 0 ∧ y 0 < 7 / 100 ∧ 1 / 25 < y 1 ∧ y 1 < 7 / 100 := by
  have h := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 100)).mp (Metric.mem_ball.mp hy)
  have h0 := h 0
  have h1 := h 1
  simp only [Real.dist_eq, pTie, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h0 h1
  rw [abs_lt] at h0 h1
  refine ⟨by linarith [h0.1], by linarith [h0.2], by linarith [h1.1], by linarith [h1.2]⟩

/-- On $V_0$ the third branch is inactive: $f_2<f_0$. -/
theorem chartTie_inactive {y : Vec 2} (hy : y ∈ chartTie) : branch 2 y < branch 0 y := by
  obtain ⟨h0, h0', h1, h1'⟩ := chartTie_bounds hy
  simp only [branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith

/-- Where $f_2<f_0$, $F=\max\{f_0,f_1\}$. -/
theorem objective_eq_max_of_inactive {y : Vec 2} (h2 : branch 2 y < branch 0 y) :
    objective y = max (branch 0 y) (branch 1 y) := by
  unfold objective
  rcases le_total (branch 1 y) (branch 2 y) with h | h
  · rw [max_eq_right h, max_eq_left h2.le, max_eq_left (h.trans h2.le)]
  · rw [max_eq_left h]

/-- The two branch gradients at $p_0$ differ, and their determinant is nonzero. -/
theorem pTie_gradients :
    PlanarQuadraticExample.gradient 0 pTie ≠ PlanarQuadraticExample.gradient 1 pTie ∧
      pairDet (PlanarQuadraticExample.gradient 0 pTie) (PlanarQuadraticExample.gradient 1 pTie)
        ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := gradient_coordinates pTie
  rw [h0, h1]
  constructor
  · intro h
    have h' := congrFun h 0
    simp only [pTie, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h'
    norm_num at h'
  · simp only [pairDet, pTie, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num

/-- $F$ is not differentiable at $p_0$: it is a corner. -/
theorem pTie_not_differentiable : ¬DifferentiableAt ℝ objective pTie := by
  intro hd
  have hg := hasFDerivAt_coordinateGradient hd
  obtain ⟨htie, hlt⟩ := pTie_tie
  have hobj : objective pTie = branch 0 pTie := by
    unfold objective
    rw [← htie, max_eq_left hlt.le, max_self]
  have h0 := PlanarCrossing.actual_gradient_eq_active_branch objective_convex
    (localFiniteMax pTie) (fun i => (branch_hasGradient i pTie).differentiableAt) hg hobj.symm
  have h1 := PlanarCrossing.actual_gradient_eq_active_branch objective_convex
    (localFiniteMax pTie) (fun i => (branch_hasGradient i pTie).differentiableAt) hg
    (hobj.trans htie).symm
  rw [coordinateGradient_eq] at h0 h1
  exact pTie_gradients.1 (h0.trans h1.symm)

/-- The standing assumptions hold for $F$, $F_*=0$, $C=\{p_0\}$ and $\ell=F(p_0)$; the
regularity at $p_0$ is the two-branch alternative, with the chart $V_0$ and the branches
$f_0,f_1$. -/
theorem nonradial_standing :
    IsLeast (range objective) 0 ∧ ({pTie} : Set (Vec 2)).Nonempty ∧
      IsCompact ({pTie} : Set (Vec 2)) ∧
      ({pTie} : Set (Vec 2)) ⊆ {x | objective x = objective pTie} ∧
      0 < objective pTie ∧
      (∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | objective u ≤ objective pTie} → x = y) ∧
      (∀ p ∈ ({pTie} : Set (Vec 2)), ¬IsAffineCritical objective p) ∧
      (∀ p ∈ ({pTie} : Set (Vec 2)),
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 objective V) ∨
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
          ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
          (∀ z ∈ V, objective z = max (f₁ z) (f₂ z)) ∧ f₁ p = objective p ∧
          f₂ p = objective p ∧
          LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) := by
  have hbox : pTie ∈ box := by
    simp only [box, mem_setOf_eq, pTie, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    norm_num [abs_of_pos]
  have hpos : 0 < objective pTie := by
    have h := objective_lower pTie
    have hs : 0 < sqNorm pTie := by
      simp only [sqNorm, Fin.sum_univ_two, pTie, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      norm_num
    linarith
  have hnc : ¬IsAffineCritical objective pTie := by
    intro hcrit
    have h0 := affineCorrect_on_box hbox hcrit
    have h := (mem_subdifferential.mp h0) 0
    simp [dot, objective_zero] at h
    linarith
  have hmax : ∀ z ∈ chartTie, objective z = max (branch 0 z) (branch 1 z) :=
    fun z hz => objective_eq_max_of_inactive (chartTie_inactive hz)
  have hact₁ : branch 0 pTie = objective pTie := by
    rw [hmax pTie pTie_mem, ← pTie_tie.1, max_self]
  refine ⟨⟨⟨0, objective_zero⟩, by rintro _ ⟨x, rfl⟩; exact objective_nonneg x⟩,
    singleton_nonempty pTie, isCompact_singleton, ?_, hpos,
    fun x y => strict_contours (objective pTie) x y, ?_, ?_⟩
  · intro x hx
    rw [mem_singleton_iff.mp hx]
    rfl
  · intro x hx
    rw [mem_singleton_iff.mp hx]
    exact hnc
  · intro x hx
    rw [mem_singleton_iff.mp hx]
    refine Or.inr ⟨chartTie, Metric.isOpen_ball, pTie_mem, branch 0, branch 1,
      (branch_convex 0).subset (subset_univ _) (convex_ball _ _),
      (branch_convex 1).subset (subset_univ _) (convex_ball _ _),
      (branch_contDiff 0).contDiffOn, (branch_contDiff 1).contDiffOn, hmax, hact₁,
      pTie_tie.1.symm.trans hact₁, ?_⟩
    apply independent_of_pairDet_ne_zero
    rw [coordinateGradient_eq, coordinateGradient_eq]
    exact pTie_gradients.2

/-- The standing assumptions of this file can all hold at once: for the objective $F$ of
Theorem `art:nonradial-example`, $F_*=0$, $C=\{p_0\}$, $\ell=F(p_0)$, $c_1=1/4$ and
$c_2=1/2$ (`nonradial_standing`). -/
example : ∃ (F : Vec 2 → ℝ) (_ : ConvexOn ℝ univ F) (Fstar : ℝ) (C : Set (Vec 2))
    (ℓ c₁ c₂ : ℝ), IsLeast (range F) Fstar ∧ C.Nonempty ∧ IsCompact C ∧ C ⊆ {x | F x = ℓ} ∧
      Fstar < ℓ ∧ (∀ x y : Vec 2, segment ℝ x y ⊆ frontier {u | F u ≤ ℓ} → x = y) ∧
      (∀ p ∈ C, ¬IsAffineCritical F p) ∧
      (∀ p ∈ C, (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ 2 F V) ∨
        (∃ V : Set (Vec 2), IsOpen V ∧ p ∈ V ∧ ∃ f₁ f₂ : Vec 2 → ℝ,
          ConvexOn ℝ V f₁ ∧ ConvexOn ℝ V f₂ ∧ ContDiffOn ℝ 2 f₁ V ∧ ContDiffOn ℝ 2 f₂ V ∧
          (∀ z ∈ V, F z = max (f₁ z) (f₂ z)) ∧ f₁ p = F p ∧ f₂ p = F p ∧
          LinearIndependent ℝ ![coordinateGradient f₁ p, coordinateGradient f₂ p])) ∧
      0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  exact ⟨objective, objective_convex, 0, {pTie}, objective pTie, 1 / 4, 1 / 2, hFstar, hCne,
    hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular, by norm_num, by norm_num, by norm_num⟩

/-- The hypotheses of `corner_curve`, `corner_velocity` and `corner_field` hold together: the
standing data above with $c_1=1/4$, $c_2=1/2$; the corner $c=p_0$ (nonsmooth by
`pTie_not_differentiable`) with the chart $V_0$ and the branches $f_0,f_1$ of the example; the
curve $p$ given by `corner_curve`; one cutoff $\chi\equiv1$, which equals one near every normal
arc; the velocity $v=p'$; and the field of the proof for these data. -/
example : True := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  have hmax : ∀ z ∈ chartTie, objective z = max (branch 0 z) (branch 1 z) :=
    fun z hz => objective_eq_max_of_inactive (chartTie_inactive hz)
  have hact₁ : branch 0 pTie = objective pTie := by
    rw [hmax pTie pTie_mem, ← pTie_tie.1, max_self]
  have hact₂ : branch 1 pTie = objective pTie := pTie_tie.1.symm.trans hact₁
  have hconv₁ : ConvexOn ℝ chartTie (branch 0) :=
    (branch_convex 0).subset (subset_univ _) (convex_ball _ _)
  have hconv₂ : ConvexOn ℝ chartTie (branch 1) :=
    (branch_convex 1).subset (subset_univ _) (convex_ball _ _)
  have hind : LinearIndependent ℝ
      ![coordinateGradient (branch 0) pTie, coordinateGradient (branch 1) pTie] := by
    apply independent_of_pairDet_ne_zero
    rw [coordinateGradient_eq, coordinateGradient_eq]
    exact pTie_gradients.2
  obtain ⟨-, pc, hpℓ, hpC, hpdef, -⟩ := corner_curve objective objective_convex 0 hFstar {pTie}
    (objective pTie) hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) pTie (mem_singleton pTie) pTie_not_differentiable
    chartTie Metric.isOpen_ball pTie_mem (branch 0) (branch 1) hconv₁ hconv₂
    (branch_contDiff 0).contDiffOn (branch_contDiff 1).contDiffOn hmax hact₁ hact₂ hind
  have _hvel := corner_velocity objective objective_convex 0 hFstar {pTie} (objective pTie) hCne
    hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) pTie (mem_singleton pTie) pTie_not_differentiable chartTie Metric.isOpen_ball
    pTie_mem (branch 0) (branch 1) hconv₁ hconv₂ (branch_contDiff 0).contDiffOn
    (branch_contDiff 1).contDiffOn hmax hact₁ hact₂ hind pc hpℓ hpC hpdef (deriv pc) rfl
  have _hfield := corner_field objective objective_convex 0 hFstar {pTie} (objective pTie) hCne
    hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) pTie (mem_singleton pTie) pTie_not_differentiable chartTie Metric.isOpen_ball
    pTie_mem (branch 0) (branch 1) hconv₁ hconv₂ (branch_contDiff 0).contDiffOn
    (branch_contDiff 1).contDiffOn hmax hact₁ hact₂ hind pc hpℓ hpC hpdef (m := 1)
    (fun _ _ => (1 : ℝ)) (fun i j hij => absurd (Subsingleton.elim i j) hij) (fun _ => deriv pc) 0
    rfl (Filter.Eventually.of_forall fun _ => rfl) _ rfl
  trivial

/-- The smooth point $x_1=(1/20,0)$ of the witnesses. -/
def xSmooth : Vec 2 := ![1 / 20, 0]

/-- The smooth point $z_1=(1/40,0)$ of the witnesses. -/
def zSmooth : Vec 2 := ![1 / 40, 0]

/-- The open region where $f_0$ is the only active branch. -/
theorem region0_open :
    IsOpen {y : Vec 2 | branch 1 y < branch 0 y ∧ branch 2 y < branch 0 y} :=
  (isOpen_lt (branch_contDiff 1 (N := 0)).continuous
    (branch_contDiff 0 (N := 0)).continuous).inter
    (isOpen_lt (branch_contDiff 2 (N := 0)).continuous (branch_contDiff 0 (N := 0)).continuous)

/-- Where $f_0$ is the only active branch, $F=f_0$ near the point, so $\nabla F=\nabla f_0$. -/
theorem objective_hasGradient_branch0 {y : Vec 2}
    (hy : branch 1 y < branch 0 y ∧ branch 2 y < branch 0 y) :
    objective y = branch 0 y ∧ objective =ᶠ[𝓝 y] branch 0 ∧
      HasFDerivAt objective (gradientFunctional (PlanarQuadraticExample.gradient 0 y)) y := by
  have he : ∀ u : Vec 2, branch 1 u < branch 0 u ∧ branch 2 u < branch 0 u →
      objective u = branch 0 u := fun u hu => by
    unfold objective
    exact max_eq_left (max_le hu.1.le hu.2.le)
  have hev : objective =ᶠ[𝓝 y] branch 0 := by
    filter_upwards [region0_open.mem_nhds hy] with u hu
    exact he u hu
  exact ⟨he y hy, hev, (branch_hasGradient 0 y).congr_of_eventuallyEq hev⟩

/-- At $x_1$ only $f_0$ is active. -/
theorem xSmooth_mem :
    branch 1 xSmooth < branch 0 xSmooth ∧ branch 2 xSmooth < branch 0 xSmooth := by
  simp only [xSmooth, branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- At $z_1$ only $f_0$ is active. -/
theorem zSmooth_mem :
    branch 1 zSmooth < branch 0 zSmooth ∧ branch 2 zSmooth < branch 0 zSmooth := by
  simp only [zSmooth, branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- $\nabla f_0(x_1)=(11/10,0)$. -/
theorem gradient0_xSmooth : PlanarQuadraticExample.gradient 0 xSmooth = ![11 / 10, 0] := by
  rw [(gradient_coordinates xSmooth).1]
  ext i
  fin_cases i <;> norm_num [xSmooth]

/-- $\nabla f_0(z_1)=(21/20,0)$. -/
theorem gradient0_zSmooth : PlanarQuadraticExample.gradient 0 zSmooth = ![21 / 20, 0] := by
  rw [(gradient_coordinates zSmooth).1]
  ext i
  fin_cases i <;> norm_num [zSmooth]

/-- The pair $x_1,z_1$ is eligible for $c_1=1/4$, $c_2=99/100$:
$d=11/400$, $\Delta=43/1600$, $t=1/800$. -/
theorem smooth_pair_eligible :
    EligiblePair objective (1 / 4) (99 / 100) xSmooth zSmooth
      (PlanarQuadraticExample.gradient 0 xSmooth) (PlanarQuadraticExample.gradient 0 zSmooth) := by
  obtain ⟨hx, -, hgx⟩ := objective_hasGradient_branch0 xSmooth_mem
  obtain ⟨hz, -, hgz⟩ := objective_hasGradient_branch0 zSmooth_mem
  refine ⟨hgx, hgz, ?_, ?_, ?_, ?_⟩
  · simp only [pairDecrease, pairStep]
    rw [gradient0_xSmooth]
    simp [dot, Fin.sum_univ_two, xSmooth, zSmooth]
    norm_num
  · rw [hx, hz]
    simp only [pairDecrease, pairStep]
    rw [gradient0_xSmooth]
    simp [dot, Fin.sum_univ_two, xSmooth, zSmooth, branch]
    norm_num
  · rw [hx, hz]
    simp only [pairDecrease, pairStep]
    rw [gradient0_xSmooth]
    simp [dot, Fin.sum_univ_two, xSmooth, zSmooth, branch]
    norm_num
  · simp only [pairDecrease, pairCurvature, pairStep]
    rw [gradient0_xSmooth, gradient0_zSmooth]
    simp [dot, Fin.sum_univ_two, xSmooth, zSmooth]
    norm_num

/-- The hypotheses of `derivative_triangular`, `determinant_derivative`, `smooth_pairing`,
`corner_field_formula` and `tangent_cancellation` hold together: the standing data with
$c_1=1/4$, $c_2=99/100$; the smooth point $x_1$, where $F=f_0$ near $x_1$ and
$\nabla F(x_1)=(11/10,0)\ne0$; the eligible pair $x_1,z_1$ (`smooth_pair_eligible`) with the
segment point $q=x_1$ ($\theta=0$); one cutoff and the constant velocity $(0,1)$; for
`derivative_triangular` and `determinant_derivative` the field of the proof, for
`smooth_pairing` the angular cutoff $\chi\equiv0$ and for `corner_field_formula`
$\chi\equiv1$, with $w(x_1)$ given by (`art:planar-field-formula`). -/
example : True := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  have hp := smooth_pair_eligible
  obtain ⟨-, hev, hgx⟩ := objective_hasGradient_branch0 xSmooth_mem
  let χ : Fin 1 → Vec 2 → ℝ := fun _ _ => 1
  have hχ : ∀ j, ContDiff ℝ ∞ (χ j) := fun _ => contDiff_const
  let v : Fin 1 → ℝ → Vec 2 := fun _ _ => ![0, 1]
  have hdiff : ∀ y ∈ {y : Vec 2 | branch 1 y < branch 0 y ∧ branch 2 y < branch 0 y},
      DifferentiableAt ℝ objective y := fun y hy =>
    (objective_hasGradient_branch0 hy).2.2.differentiableAt
  have hFx : ContDiffAt ℝ 2 objective xSmooth :=
    (branch_contDiff 0).contDiffAt.congr_of_eventuallyEq hev
  have hcg : coordinateGradient objective xSmooth = ![11 / 10, 0] := by
    rw [← gradient0_xSmooth]
    exact AffineProjection.gradientFunctional_injective
      ((hasFDerivAt_coordinateGradient hgx.differentiableAt).unique hgx)
  have hgx0 : coordinateGradient objective xSmooth ≠ 0 := by
    rw [hcg]
    intro h
    have := congrFun h 0
    norm_num at this
  have hw : ∀ᶠ y in 𝓝 xSmooth, ∀ φ, normal φ = normalized (coordinateGradient objective y) →
      PlanarObjectiveField.field objective_convex χ v y =
        fieldFormula (fun j ψ => χ j (normal ψ)) v (objective y) φ := by
    filter_upwards [region0_open.mem_nhds xSmooth_mem] with y hy φ hφ
    exact field_eq_fieldFormula objective_convex χ (fun j => (hχ j).differentiable (by simp)) v
      (hasFDerivAt_coordinateGradient (hdiff y hy)) φ hφ
  have hxq : xSmooth = xSmooth + (0 : ℝ) • (zSmooth - xSmooth) := by simp
  have _h1 := derivative_triangular objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) χ hχ v (PlanarObjectiveField.field objective_convex χ v) xSmooth hFx hgx0
    (fun _ => contDiffAt_const) hw _ _ rfl rfl _ _ _ rfl rfl rfl
  have _h2 := determinant_derivative objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) χ hχ v (PlanarObjectiveField.field objective_convex χ v) xSmooth zSmooth _ _ hp
    (zSmooth - xSmooth) rfl 0 ⟨le_rfl, zero_le_one⟩ xSmooth hxq hFx hgx0
    (fun _ => contDiffAt_const) hw _ _ rfl rfl _ _ _ rfl rfl rfl _ _ rfl rfl
  have hg0 : PlanarQuadraticExample.gradient 0 xSmooth ≠ 0 := by
    rw [gradient0_xSmooth]
    intro h
    have := congrFun h 0
    norm_num at this
  obtain ⟨θ, hθ⟩ := exists_angle _ (PlanarObjectiveField.normalized_sqNorm hg0)
  have _h3 := smooth_pairing objective objective_convex 0 hFstar {pTie} (objective pTie) hCne
    hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) (m := 1) (fun _ _ => (0 : ℝ)) (fun _ _ => ⟨le_rfl, zero_le_one⟩)
    (fun i j hij => absurd (Subsingleton.elim i j) hij) v
    (fun _ => fieldFormula (fun _ _ => (0 : ℝ)) v (objective xSmooth) θ) xSmooth _ hgx hg0 θ hθ
    rfl (fun _ hj => (hj rfl).elim)
  have _h4 := corner_field_formula objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) (m := 1) (fun _ _ => (1 : ℝ)) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    v (fun _ => fieldFormula (fun _ _ => (1 : ℝ)) v (objective xSmooth) θ) xSmooth _ hgx θ hθ rfl
    0 (Filter.Eventually.of_forall fun _ => rfl)
  have _h5 := tangent_cancellation objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) (m := 1) (fun _ _ => (0 : ℝ)) (fun _ => contDiff_const) v (objective xSmooth) _
    rfl 0
  trivial

/-- The hypotheses of `log_determinant_derivative_bound` and `derivative_coefficients_bounded`
hold together for the objects that the library's construction produces for the standing data
with $c_1=1/4$, $c_2=1/2$: cutoffs and velocities, the field of the proof, its neighborhood $N$
(`PlanarAllPairs.exists_all_endpoint_field`), and $U$, $Q$, $\kappa$, $\delta$ with the
transversality of eligible segments (`PlanarAllPairs.structured_all_pair_transport`). -/
example : True := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  obtain ⟨m, χ, v, hχ, N, η, hη, hN, hKN, hLip, hvis, hv, hstruct, hcommon, -⟩ :=
    PlanarAllPairs.exists_all_endpoint_field objective_convex hCcpt (fun x hx => hCℓ hx) hstrict
      (fun x hx => regularity_of_literal (hregular x hx)) hnoncrit (σ := 1 / 2) (by norm_num)
  obtain ⟨U, Q, -, -, -, hQ, hQN, κ, δ, _C, hκ, hδ, -, hpairs⟩ :=
    PlanarAllPairs.structured_all_pair_transport objective_convex hCcpt hN hKN hχ hη hLip hvis hv
      hstruct hcommon (c₁ := 1 / 4) (c₂ := 1 / 2) (by norm_num) (by norm_num)
  have _h1 := log_determinant_derivative_bound objective objective_convex 0 hFstar {pTie}
    (objective pTie) hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) χ hχ v (PlanarObjectiveField.field objective_convex χ v) rfl U Q
    N hQ hN hQN hLip (fun p hp => hv p (hQN hp)) (fun p hp => hstruct p (hQN hp)) η hη
    (fun p hp => hvis p (hQN hp)) κ δ hκ hδ (fun x hx z hz g h hp hs θ hθ =>
      (hpairs x hx z hz g h hp ((PlanarCrossing.pi_norm_le_euclidean_norm _).trans_lt hs)).1 θ hθ)
  have _h2 := derivative_coefficients_bounded objective objective_convex 0 hFstar {pTie}
    (objective pTie) hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (PlanarObjectiveField.field objective_convex χ v) Q N hQ hN hQN
    hLip
  trivial

/-- The hypotheses of `comparison_functions`, `log_determinant_increment`,
`transport_constants` and `one_sided_comparison` hold together: the standing data with
$c_1=1/4$, $c_2=99/100$; the eligible pair $x_1,z_1$; the constant field $w\equiv(0,1)$, for
which $D\equiv\det(z_1-x_1,(0,1))=-1/40\ne0$ and $H$ is constant; and $A=0$. -/
example : True := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  have hp := smooth_pair_eligible
  have hdet0 : pairDet (zSmooth - xSmooth) ![0, 1] ≠ 0 := by
    simp [pairDet, zSmooth, xSmooth]
    norm_num
  have hbound : ∀ θ ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun _ : ℝ => Real.log |pairDet (zSmooth - xSmooth) ![0, 1]|)
        (derivWithin (fun _ : ℝ => Real.log |pairDet (zSmooth - xSmooth) ![0, 1]|) (Ioi θ) θ)
        (Ici θ) θ ∧
      |derivWithin (fun _ : ℝ => Real.log |pairDet (zSmooth - xSmooth) ![0, 1]|) (Ioi θ) θ| ≤
        0 * |derivWithin (fun θ => objective (xSmooth + θ • (zSmooth - xSmooth))) (Ioi θ) θ| ∧
      0 * |derivWithin (fun θ => objective (xSmooth + θ • (zSmooth - xSmooth))) (Ioi θ) θ| ≤
        0 * (derivWithin (fun θ => objective (xSmooth + θ • (zSmooth - xSmooth))) (Ioi θ) θ +
          2 * -dot (PlanarQuadraticExample.gradient 0 xSmooth) (zSmooth - xSmooth)) := by
    intro θ _
    rw [derivWithin_const]
    exact ⟨hasDerivWithinAt_const _ _ _, by simp, by simp⟩
  have _h1 := comparison_functions objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => ![0, 1]) xSmooth zSmooth _ _ hp (zSmooth - xSmooth) rfl _ rfl
    (fun θ => xSmooth + θ • (zSmooth - xSmooth)) rfl
    (fun θ => objective (xSmooth + θ • (zSmooth - xSmooth)))
    (fun _ => pairDet (zSmooth - xSmooth) ![0, 1])
    (fun _ => Real.log |pairDet (zSmooth - xSmooth) ![0, 1]|) rfl rfl rfl continuousOn_const
    (fun _ _ => hdet0) 0 le_rfl hbound 1 (Or.inl rfl) _ rfl
  have _h2 := log_determinant_increment objective objective_convex 0 hFstar {pTie}
    (objective pTie) hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => ![0, 1]) xSmooth zSmooth _ _ hp
    (zSmooth - xSmooth) rfl _ rfl (fun θ => xSmooth + θ • (zSmooth - xSmooth)) rfl
    (fun θ => objective (xSmooth + θ • (zSmooth - xSmooth)))
    (fun _ => pairDet (zSmooth - xSmooth) ![0, 1])
    (fun _ => Real.log |pairDet (zSmooth - xSmooth) ![0, 1]|) rfl rfl rfl continuousOn_const
    (fun _ _ => hdet0) 0 le_rfl hbound
  have _h3 := transport_constants objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => ![0, 1]) xSmooth zSmooth _ _ hp (zSmooth - xSmooth) rfl _ rfl
    (fun θ => xSmooth + θ • (zSmooth - xSmooth)) rfl
    (fun θ => objective (xSmooth + θ • (zSmooth - xSmooth)))
    (fun _ => pairDet (zSmooth - xSmooth) ![0, 1])
    (fun _ => Real.log |pairDet (zSmooth - xSmooth) ![0, 1]|) rfl rfl rfl continuousOn_const
    (fun _ _ => hdet0) 0 le_rfl hbound _ rfl
  have _h4 := one_sided_comparison (fun _ => 0) (fun _ => 0) continuousOn_const
    (fun θ _ => hasDerivWithinAt_const θ _ 0) (fun _ _ => le_rfl)
  trivial

/-- The hypotheses of `transversality_limits`, which do not include eligibility, hold together:
the standing data with $c_1=1/4$, $c_2=1/2$; $Q=\{x_1\}$, where $\partial F(x_1)=\{(11/10,0)\}$;
the constant field $w\equiv(1,0)$ with $\eta=1$; the constant sequences $x_k=x_1$ and
$g_k=h_k=\bar g=\bar h=\nabla F(x_1)$; and $z_k=x_1+(k+1)^{-1}\hat s$ with
$\hat s=(-1,0)=-w(x_1)/\norm{w(x_1)}$. With eligible pairs these assumptions cannot hold
together, which is the contradiction of the proof (`transversality_contradiction`). -/
example : True := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  obtain ⟨-, -, hgx⟩ := objective_hasGradient_branch0 xSmooth_mem
  have hsub : ∀ a ∈ subdifferential objective xSmooth,
      a = PlanarQuadraticExample.gradient 0 xSmooth :=
    fun a ha => supporting_vector_eq_gradient ha hgx
  have hgmem : PlanarQuadraticExample.gradient 0 xSmooth ∈ subdifferential objective xSmooth :=
    convex_supporting_inequality objective_convex hgx
  have hunit : sqNorm (![1, 0] : Vec 2) = 1 := by simp [sqNorm]
  have hunit' : sqNorm (![-1, 0] : Vec 2) = 1 := by simp [sqNorm]
  have hshat_eq : (![-1, 0] : Vec 2) =
      -normalized ((fun _ : Vec 2 => (![1, 0] : Vec 2)) xSmooth) := by
    rw [normalized_of_sqNorm_eq_one hunit]
    ext i
    fin_cases i <;> simp
  have hvis : ∀ p ∈ ({xSmooth} : Set (Vec 2)), ∀ a ∈ subdifferential objective p,
      (1 : ℝ) ≤ dot a ((fun _ : Vec 2 => (![1, 0] : Vec 2)) p) := by
    intro p hp a ha
    rw [mem_singleton_iff.mp hp] at ha
    rw [hsub a ha, gradient0_xSmooth]
    simp [dot]
    norm_num
  have hcommon : ∀ p ∈ ({xSmooth} : Set (Vec 2)), ∀ a ∈ subdifferential objective p,
      ∀ b ∈ subdifferential objective p, dot a ((fun _ : Vec 2 => (![1, 0] : Vec 2)) p) =
        dot b ((fun _ : Vec 2 => (![1, 0] : Vec 2)) p) := by
    intro p hp a ha b hb
    rw [mem_singleton_iff.mp hp] at ha hb
    rw [hsub a ha, hsub b hb]
  have hstep : ∀ k : ℕ, (xSmooth + (1 / ((k : ℝ) + 1)) • (![-1, 0] : Vec 2)) - xSmooth =
      (1 / ((k : ℝ) + 1)) • (![-1, 0] : Vec 2) := fun k => by abel
  have hs0 : ∀ k : ℕ, (xSmooth + (1 / ((k : ℝ) + 1)) • (![-1, 0] : Vec 2)) - xSmooth ≠ 0 := by
    intro k
    rw [hstep k]
    refine smul_ne_zero (by positivity) ?_
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hcoal : Tendsto (fun k : ℕ => (xSmooth + (1 / ((k : ℝ) + 1)) • (![-1, 0] : Vec 2)) -
      xSmooth) atTop (𝓝 0) := by
    simp_rw [hstep]
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.smul_const (![-1, 0] : Vec 2)
  have hdir : Tendsto (fun k : ℕ => normalized ((xSmooth + (1 / ((k : ℝ) + 1)) •
      (![-1, 0] : Vec 2)) - xSmooth)) atTop (𝓝 ![-1, 0]) := by
    have he : ∀ k : ℕ, normalized ((xSmooth + (1 / ((k : ℝ) + 1)) • (![-1, 0] : Vec 2)) -
        xSmooth) = ![-1, 0] := fun k => by
      rw [hstep, normalized_smul_of_pos (by positivity), normalized_of_sqNorm_eq_one hunit']
    simp_rw [he]
    exact tendsto_const_nhds
  have _h := transversality_limits objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => ![1, 0]) {xSmooth} 1 one_pos hvis hcommon (fun _ => xSmooth)
    (fun k => xSmooth + (1 / ((k : ℝ) + 1)) • (![-1, 0] : Vec 2))
    (fun _ => PlanarQuadraticExample.gradient 0 xSmooth)
    (fun _ => PlanarQuadraticExample.gradient 0 xSmooth) hs0 hcoal xSmooth (mem_singleton _)
    tendsto_const_nhds ![-1, 0] (PlanarQuadraticExample.gradient 0 xSmooth)
    (PlanarQuadraticExample.gradient 0 xSmooth) hdir tendsto_const_nhds tendsto_const_nhds hgmem
    hgmem hshat_eq _ _ (fun _ => rfl) (fun _ => rfl)
  trivial

/-- The hypotheses of `branch_cocoercivity` and `same_branch_secant` hold together: the
standing data with $c_1=1/4$, $c_2=99/100$; the branch $f=f_0$, convex and $C^2$ on the chart
$V=\R^2$, with $\nabla f_0$ $2$-Lipschitz; the buffer $B=\R^2$ with $\rho=1$; the eligible
pair $x_1,z_1$, at both ends of which $f_0$ is the active branch; and $w\equiv0$, $G=0$. -/
example : True := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  have hp := smooth_pair_eligible
  obtain ⟨hx, -, -⟩ := objective_hasGradient_branch0 xSmooth_mem
  obtain ⟨hz, -, -⟩ := objective_hasGradient_branch0 zSmooth_mem
  have hLip : ∀ u ∈ (univ : Set (Vec 2)), ∀ u' ∈ (univ : Set (Vec 2)),
      ‖euclideanVector (coordinateGradient (branch 0) u - coordinateGradient (branch 0) u')‖ ≤
        2 * ‖euclideanVector (u - u')‖ := by
    intro u _ u' _
    apply euclid_le_mul_of_sqNorm_le (by norm_num)
    rw [coordinateGradient_eq, coordinateGradient_eq, (gradient_coordinates u).1,
      (gradient_coordinates u').1]
    simp only [sqNorm, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    nlinarith [sq_nonneg (u 0 - u' 0), sq_nonneg (u 1 - u' 1)]
  have hxz : ‖euclideanVector (zSmooth - xSmooth)‖ < 1 := by
    refine lt_of_le_of_lt (euclid_le_of_sqNorm_le (c := 1 / 40) (by norm_num) ?_) (by norm_num)
    simp [sqNorm, xSmooth, zSmooth]
    norm_num
  have hBV : ∀ u ∈ (univ : Set (Vec 2)), ∀ u' : Vec 2,
      ‖euclideanVector (u' - u)‖ < 1 → u' ∈ (univ : Set (Vec 2)) := fun _ _ _ _ => mem_univ _
  have _h1 := branch_cocoercivity objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) (branch 0) univ isOpen_univ (branch_convex 0) (branch_contDiff 0).contDiffOn 2
    two_pos hLip univ 1 one_pos hBV xSmooth zSmooth _ _ hp hx.symm hz.symm (mem_univ _)
    (mem_univ _) hxz
  have _h2 := same_branch_secant objective objective_convex 0 hFstar {pTie} (objective pTie)
    hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (99 / 100) (by norm_num) (by norm_num)
    (by norm_num) (branch 0) univ isOpen_univ (branch_convex 0) (branch_contDiff 0).contDiffOn 2
    two_pos hLip univ 1 one_pos hBV xSmooth zSmooth _ _ hp hx.symm hz.symm
    (coordinateGradient_eq 0 xSmooth) (coordinateGradient_eq 0 zSmooth) (mem_univ _)
    (mem_univ _) hxz (fun _ => 0) 0 (by simp [euclideanVector])
  trivial

/-- Points of $V_0$ by their coordinates. -/
theorem mem_chartTie_of {y : Vec 2} (h0 : |y 0 - 40 / 721| < 1 / 100)
    (h1 : |y 1 - 39 / 721| < 1 / 100) : y ∈ chartTie := by
  apply Metric.mem_ball.mpr
  apply (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 100)).mpr
  intro i
  fin_cases i
  · simpa [Real.dist_eq, pTie] using h0
  · simpa [Real.dist_eq, pTie] using h1

/-- The crossing point $x_2=(40/721,\,39/721+1/1000)$, where $f_1$ is the only active branch. -/
def xCross : Vec 2 := ![40 / 721, 39 / 721 + 1 / 1000]

/-- The crossing point $z_2=(40/721,\,39/721-1/1000)$, where $f_0$ is the only active branch. -/
def zCross : Vec 2 := ![40 / 721, 39 / 721 - 1 / 1000]

/-- $x_2\in V_0$. -/
theorem xCross_mem : xCross ∈ chartTie :=
  mem_chartTie_of (by norm_num [xCross]) (by norm_num [xCross, abs_of_pos])

/-- $z_2\in V_0$. -/
theorem zCross_mem : zCross ∈ chartTie :=
  mem_chartTie_of (by norm_num [zCross]) (by norm_num [zCross, abs_of_neg])

/-- At $x_2$ only $f_1$ is active. -/
theorem xCross_active : branch 0 xCross < branch 1 xCross ∧ branch 2 xCross < branch 1 xCross := by
  simp only [xCross, branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- At $z_2$ only $f_0$ is active. -/
theorem zCross_active : branch 1 zCross < branch 0 zCross ∧ branch 2 zCross < branch 0 zCross := by
  simp only [zCross, branch, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- Where $f_1$ is the only active branch, $F=f_1$ near the point, so $\nabla F=\nabla f_1$. -/
theorem objective_hasGradient_branch1 {y : Vec 2}
    (hy : branch 0 y < branch 1 y ∧ branch 2 y < branch 1 y) :
    objective y = branch 1 y ∧
      HasFDerivAt objective (gradientFunctional (PlanarQuadraticExample.gradient 1 y)) y := by
  have he : ∀ u : Vec 2, branch 0 u < branch 1 u ∧ branch 2 u < branch 1 u →
      objective u = branch 1 u := fun u hu => by
    unfold objective
    rw [max_eq_left hu.2.le, max_eq_right hu.1.le]
  have hopen : IsOpen {u : Vec 2 | branch 0 u < branch 1 u ∧ branch 2 u < branch 1 u} :=
    (isOpen_lt (branch_contDiff 0 (N := 0)).continuous
      (branch_contDiff 1 (N := 0)).continuous).inter
      (isOpen_lt (branch_contDiff 2 (N := 0)).continuous (branch_contDiff 1 (N := 0)).continuous)
  have hev : objective =ᶠ[𝓝 y] branch 1 := by
    filter_upwards [hopen.mem_nhds hy] with u hu
    exact he u hu
  exact ⟨he y hy, (branch_hasGradient 1 y).congr_of_eventuallyEq hev⟩

/-- The pair $x_2,z_2$ crosses the switching curve and is eligible for $c_1=1/4$, $c_2=1/2$. -/
theorem cross_pair_eligible :
    EligiblePair objective (1 / 4) (1 / 2) xCross zCross
      (PlanarQuadraticExample.gradient 1 xCross) (PlanarQuadraticExample.gradient 0 zCross) := by
  obtain ⟨hx, hgx⟩ := objective_hasGradient_branch1 xCross_active
  obtain ⟨hz, -, hgz⟩ := objective_hasGradient_branch0 zCross_active
  refine ⟨hgx, hgz, ?_, ?_, ?_, ?_⟩
  · simp only [pairDecrease, pairStep]
    rw [(gradient_coordinates xCross).2.1]
    simp [dot, Fin.sum_univ_two, xCross, zCross]
    norm_num
  · rw [hx, hz]
    simp only [pairDecrease, pairStep]
    rw [(gradient_coordinates xCross).2.1]
    simp [dot, Fin.sum_univ_two, xCross, zCross, branch]
    norm_num
  · rw [hx, hz]
    simp only [pairDecrease, pairStep]
    rw [(gradient_coordinates xCross).2.1]
    simp [dot, Fin.sum_univ_two, xCross, zCross, branch]
    norm_num
  · simp only [pairDecrease, pairCurvature, pairStep]
    rw [(gradient_coordinates xCross).2.1, (gradient_coordinates zCross).1]
    simp [dot, Fin.sum_univ_two, xCross, zCross]
    norm_num

/-- $\nabla f_0$ and $\nabla f_1$ are $3$-Lipschitz (Euclidean norms). -/
theorem branch_gradient_lipschitz (i : Fin 2) (u u' : Vec 2) :
    ‖euclideanVector (coordinateGradient (![branch 0, branch 1] i) u -
      coordinateGradient (![branch 0, branch 1] i) u')‖ ≤ 3 * ‖euclideanVector (u - u')‖ := by
  apply euclid_le_mul_of_sqNorm_le (by norm_num)
  fin_cases i
  · change sqNorm (coordinateGradient (branch 0) u - coordinateGradient (branch 0) u') ≤ _
    rw [coordinateGradient_eq, coordinateGradient_eq, (gradient_coordinates u).1,
      (gradient_coordinates u').1]
    simp only [sqNorm, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    nlinarith [sq_nonneg (u 0 - u' 0), sq_nonneg (u 1 - u' 1)]
  · change sqNorm (coordinateGradient (branch 1) u - coordinateGradient (branch 1) u') ≤ _
    rw [coordinateGradient_eq, coordinateGradient_eq, (gradient_coordinates u).2.1,
      (gradient_coordinates u').2.1]
    simp only [sqNorm, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    nlinarith [sq_nonneg (u 0 - u' 0), sq_nonneg (u 1 - u' 1)]

/-- On $V_0$ both branch gradients have Euclidean norm at most $2$. -/
theorem chartTie_gradient_bound (i : Fin 2) {u : Vec 2} (hu : u ∈ chartTie) :
    ‖euclideanVector (coordinateGradient (![branch 0, branch 1] i) u)‖ ≤ 2 := by
  obtain ⟨h0, h0', h1, h1'⟩ := chartTie_bounds hu
  apply euclid_le_of_sqNorm_le (by norm_num)
  fin_cases i
  · change sqNorm (coordinateGradient (branch 0) u) ≤ _
    rw [coordinateGradient_eq, (gradient_coordinates u).1]
    simp only [sqNorm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    nlinarith
  · change sqNorm (coordinateGradient (branch 1) u) ≤ _
    rw [coordinateGradient_eq, (gradient_coordinates u).2.1]
    simp only [sqNorm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    nlinarith

/-- The field of the crossing witness, $w(y)=(1+2y_1,\,1+y_0)$, which pairs equally with
$\nabla f_0(y)$ and $\nabla f_1(y)$ at every $y$. -/
def fieldCross (y : Vec 2) : Vec 2 := ![1 + 2 * y 1, 1 + y 0]

/-- $w$ is $2$-Lipschitz and bounded by $3$ on $V_0$ (Euclidean norms). -/
theorem fieldCross_bounds :
    (∀ u ∈ chartTie, ∀ u' ∈ chartTie, ‖euclideanVector (fieldCross u - fieldCross u')‖ ≤
      2 * ‖euclideanVector (u - u')‖) ∧ ∀ u ∈ chartTie, ‖euclideanVector (fieldCross u)‖ ≤ 3 := by
  refine ⟨fun u _ u' _ => ?_, fun u hu => ?_⟩
  · apply euclid_le_mul_of_sqNorm_le (by norm_num)
    simp only [fieldCross, sqNorm, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    nlinarith [sq_nonneg (u 0 - u' 0), sq_nonneg (u 1 - u' 1)]
  · obtain ⟨h0, h0', h1, h1'⟩ := chartTie_bounds hu
    apply euclid_le_of_sqNorm_le (by norm_num)
    simp only [fieldCross, sqNorm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    nlinarith

/-- On $V_0$ all subgradients of $F$ have the same pairing with $w$: $\partial F(y)$ is the
convex hull of the active gradients among $\nabla f_0(y),\nabla f_1(y)$, which pair equally
with $w(y)$. -/
theorem fieldCross_common {u : Vec 2} (hu : u ∈ chartTie) :
    ∀ a ∈ subdifferential objective u, ∀ b ∈ subdifferential objective u,
      dot a (fieldCross u) = dot b (fieldCross u) := by
  have hsub := subdifferential_eq_active_convexHull objective_convex (localFiniteMax u)
    (fun i => branch_hasGradient i u)
  set c := dot (PlanarQuadraticExample.gradient 0 u) (fieldCross u) with hc
  have hgen : (fun i => PlanarQuadraticExample.gradient i u) ''
      ↑(activeIndices objective branch u) ⊆ {a | dot a (fieldCross u) = c} := by
    rintro _ ⟨i, hi, rfl⟩
    rw [Finset.mem_coe, mem_activeIndices] at hi
    fin_cases i
    · rfl
    · change dot (PlanarQuadraticExample.gradient 1 u) (fieldCross u) = c
      rw [hc, (gradient_coordinates u).1, (gradient_coordinates u).2.1]
      simp only [fieldCross, dot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      ring
    · exfalso
      have h2 := chartTie_inactive hu
      have h0 := branch_le_objective 0 u
      exact absurd hi (ne_of_lt (h2.trans_le h0))
  have hconv : Convex ℝ {a : Vec 2 | dot a (fieldCross u) = c} := by
    intro a ha b hb s t _ _ hst
    simp only [mem_setOf_eq] at ha hb ⊢
    change dotProduct (s • a + t • b) (fieldCross u) = c
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
    change s * dot a (fieldCross u) + t * dot b (fieldCross u) = c
    rw [ha, hb, ← add_mul, hst, one_mul]
  have hall : ∀ a ∈ subdifferential objective u, dot a (fieldCross u) = c := by
    intro a ha
    rw [hsub] at ha
    exact convexHull_min hgen hconv ha
  intro a ha b hb
  rw [hall a ha, hall b hb]

/-- On $V_0$ the two gradient rows are uniformly independent:
$\norm{v}\le2(|\nabla f_0(y)^Tv|+|\nabla f_1(y)^Tv|)$. -/
theorem chartTie_rows {u : Vec 2} (hu : u ∈ chartTie) (v : Vec 2) :
    ‖euclideanVector v‖ ≤ 2 * (|dot (coordinateGradient (![branch 0, branch 1] 0) u) v| +
      |dot (coordinateGradient (![branch 0, branch 1] 1) u) v|) := by
  obtain ⟨h0, h0', h1, h1'⟩ := chartTie_bounds hu
  change ‖euclideanVector v‖ ≤ 2 * (|dot (coordinateGradient (branch 0) u) v| +
    |dot (coordinateGradient (branch 1) u) v|)
  rw [coordinateGradient_eq, coordinateGradient_eq, (gradient_coordinates u).1,
    (gradient_coordinates u).2.1]
  have he : ‖euclideanVector v‖ ≤ |v 0| + |v 1| := by
    apply euclid_le_of_sqNorm_le (by positivity)
    simp only [sqNorm, Fin.sum_univ_two]
    nlinarith [sq_abs (v 0), sq_abs (v 1), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))]
  have ha : (1 + 2 * u 0) * |v 0| - u 1 * |v 1| ≤ |dot ![1 + 2 * u 0, u 1] v| := by
    have hd : dot ![1 + 2 * u 0, u 1] v = (1 + 2 * u 0) * v 0 + u 1 * v 1 := by
      simp [dot, Fin.sum_univ_two]
    have h := abs_sub_abs_le_abs_sub ((1 + 2 * u 0) * v 0) (-(u 1 * v 1))
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + 2 * u 0),
      abs_of_pos (by linarith : (0 : ℝ) < u 1)] at h
    rw [hd]
    exact h
  have hb : (1 + 3 * u 1) * |v 1| - u 0 * |v 0| ≤ |dot ![u 0, 1 + 3 * u 1] v| := by
    have hd : dot ![u 0, 1 + 3 * u 1] v = (1 + 3 * u 1) * v 1 + u 0 * v 0 := by
      simp [dot, Fin.sum_univ_two]
      ring
    have h := abs_sub_abs_le_abs_sub ((1 + 3 * u 1) * v 1) (-(u 0 * v 0))
    rw [abs_neg, sub_neg_eq_add, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + 3 * u 1),
      abs_of_pos (by linarith : (0 : ℝ) < u 0)] at h
    rw [hd]
    exact h
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), mul_nonneg (by linarith : (0 : ℝ) ≤ u 0)
    (abs_nonneg (v 0)), mul_nonneg (by linarith : (0 : ℝ) ≤ u 1) (abs_nonneg (v 1))]

/-- The hypotheses of `crossing_tie_point`, `crossing_numerator`, `crossing_pairings`,
`crossing_step_bound` and `crossing_secant` hold together: the standing data with $c_1=1/4$,
$c_2=1/2$; the two-branch chart $V_0$ with $F=\max\{f_0,f_1\}$, $M=3$, $H_b=2$; the field
$w(y)=(1+2y_1,1+y_0)$ (`fieldCross`), $2$-Lipschitz, bounded by $3$ and with equal pairing on
$V_0$; $A_2=2$; and the eligible pair $x_2,z_2$ (`cross_pair_eligible`), with branch $f_1$
active at $x_2$ and $f_0$ at $z_2$, for which $A_2M\norm{s}=6/500\le1/2$. -/
example : True := by
  obtain ⟨hFstar, hCne, hCcpt, hCℓ, hpos, hstrict, hnoncrit, hregular⟩ := nonradial_standing
  have hp := cross_pair_eligible
  let f : Fin 2 → Vec 2 → ℝ := ![branch 0, branch 1]
  have hfconv : ∀ i, ConvexOn ℝ chartTie (f i) := by
    intro i
    fin_cases i
    · exact (branch_convex 0).subset (subset_univ _) (convex_ball _ _)
    · exact (branch_convex 1).subset (subset_univ _) (convex_ball _ _)
  have hfC : ∀ i, ContDiffOn ℝ 2 (f i) chartTie := by
    intro i
    fin_cases i
    · exact (branch_contDiff 0).contDiffOn
    · exact (branch_contDiff 1).contDiffOn
  have hmax : ∀ u ∈ chartTie, objective u = max (f 0 u) (f 1 u) :=
    fun u hu => objective_eq_max_of_inactive (chartTie_inactive hu)
  have hLip : ∀ i, ∀ u ∈ chartTie, ∀ u' ∈ chartTie,
      ‖euclideanVector (coordinateGradient (f i) u - coordinateGradient (f i) u')‖ ≤
        3 * ‖euclideanVector (u - u')‖ := fun i u _ u' _ => branch_gradient_lipschitz i u u'
  have hx1 : f 1 xCross = objective xCross := (objective_hasGradient_branch1 xCross_active).1.symm
  have hz0 : f 0 zCross = objective zCross :=
    (objective_hasGradient_branch0 zCross_active).1.symm
  have hij : (1 : Fin 2) ≠ 0 := by decide
  have _h1 := crossing_tie_point objective objective_convex 0 hFstar {pTie} (objective pTie) hCne
    hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) f chartTie (convex_ball _ _) Metric.isOpen_ball hfconv hfC hmax fieldCross
    (fun p hp => fieldCross_common hp) xCross zCross _ _ xCross_mem zCross_mem hp 1 0 hij hx1 hz0
  obtain ⟨A₁, hA₁, hnum⟩ := crossing_numerator objective objective_convex 0 hFstar {pTie}
    (objective pTie) hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) f chartTie (convex_ball _ _) Metric.isOpen_ball hfconv hfC hmax 3
    (by norm_num) hLip 2 (fun i u hu => chartTie_gradient_bound i hu) fieldCross 2 3
    fieldCross_bounds.1 fieldCross_bounds.2 (fun p hp => fieldCross_common hp)
  have _h3 := crossing_pairings objective objective_convex 0 hFstar {pTie} (objective pTie) hCne
    hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) f chartTie (convex_ball _ _) Metric.isOpen_ball hfconv hfC hmax 3 (by norm_num)
    hLip xCross zCross _ _ xCross_mem zCross_mem hp 1 0 hij hx1 hz0 _ _ rfl rfl _ _ rfl rfl _ rfl
  obtain ⟨hstep₁, hstep₂⟩ := crossing_step_bound objective objective_convex 0 hFstar {pTie}
    (objective pTie) hCne hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) f chartTie (convex_ball _ _) Metric.isOpen_ball hfconv hfC hmax 3
    (by norm_num) hLip 2 (by norm_num) (fun u hu v => chartTie_rows hu v) xCross zCross _ _
    xCross_mem zCross_mem hp 1 0 hij hx1 hz0 _ _ rfl rfl _ _ rfl rfl _ rfl
  have hs : ‖euclideanVector (zCross - xCross)‖ ≤ 1 / 500 := by
    apply euclid_le_of_sqNorm_le (by norm_num)
    simp [sqNorm, xCross, zCross]
    norm_num
  have _h5 := crossing_secant objective objective_convex 0 hFstar {pTie} (objective pTie) hCne
    hCcpt hCℓ hpos hstrict hnoncrit hregular (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) fieldCross xCross zCross _ _ hp _ _ rfl rfl _ _ rfl rfl 3 A₁ 2 (by norm_num) hA₁
    (by norm_num) (hnum xCross zCross _ _ xCross_mem zCross_mem hp 1 0 hij hx1 hz0)
    (hstep₁.trans hstep₂) (by nlinarith [hs]) _ rfl
  trivial

end NonVacuity

end BfgsCoverage.Article.PlanarGeometry
