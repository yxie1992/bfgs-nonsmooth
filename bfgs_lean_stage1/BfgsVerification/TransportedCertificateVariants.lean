import BfgsVerification.TransportedNormalization
import BfgsVerification.TransportedCertificateConvergence
import BfgsVerification.RadialCertificate

/-! Module T's rank-one and radial specializations. Every matrix here is actual,
and all endpoint hypotheses remain objective-only eligible-pair conditions. -/
noncomputable section
open scoped BigOperators Topology
open Matrix Set Filter

namespace BfgsVerification
namespace TransportedCertificate

theorem stepProjector_mulVec_self {n : ℕ} (s : Vec n) :
    (stepProjector s).mulVec s = 0 := by
  by_cases hs : s = 0
  · simp [hs]
  have hn : sqNorm s ≠ 0 := by
    intro hz
    apply hs
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (s j))).mp hz i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  have hd : dot s s = sqNorm s := by simp only [dot, sqNorm, pow_two]
  rw [stepProjector, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc, outer_mulVec, hd, smul_smul, inv_mul_cancel₀ hn,
    one_smul, sub_self]

theorem projected_outer {n : ℕ} (s v : Vec n) :
    stepProjector s * outer v v * stepProjector s =
      outer ((stepProjector s).mulVec v) ((stepProjector s).mulVec v) := by
  rw [BFGSCompression.mul_outer, BFGSCompression.outer_mul, (stepProjector_isSymm s).eq]


theorem stepProjector_fixes_perpendicular {n : ℕ} (s v : Vec n)
    (hv : dot v s = 0) : (stepProjector s).mulVec v = v := by
  have hh : dot s v = 0 := (dotProduct_comm s v).trans hv
  rw [stepProjector, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc, outer_mulVec, hh, zero_smul, smul_zero, sub_zero]

theorem stepProjector_perpendicular {n : ℕ} (s v : Vec n) :
    dot ((stepProjector s).mulVec v) s = 0 := by
  rw [show dot ((stepProjector s).mulVec v) s = dot s ((stepProjector s).mulVec v)
    from dotProduct_comm _ _]
  change s ⬝ᵥ (stepProjector s).mulVec v = 0
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, (stepProjector_isSymm s).eq,
    stepProjector_mulVec_self, zero_dotProduct]

theorem projected_energy {n : ℕ} (W : Mat n) (s v : Vec n) :
    metricEnergy (stepProjector s * W * stepProjector s) v =
      metricEnergy W ((stepProjector s).mulVec v) := by
  simpa only [(stepProjector_isSymm s).eq] using metricEnergy_congruence W (stepProjector s) v

/-- The projected Loewner condition is exactly the quadratic comparison on
step-perpendicular vectors. This includes dimension zero and zero step. -/
theorem projected_transport_iff_perpendicular {n : ℕ} (W Z : Mat n)
    (hW : W.IsSymm) (hZ : Z.IsSymm) (s : Vec n) (a : ℝ) :
    (a • (stepProjector s * W * stepProjector s) -
      stepProjector s * Z * stepProjector s).PosSemidef ↔
      ∀ v : Vec n, dot v s = 0 → metricEnergy Z v ≤ a * metricEnergy W v := by
  constructor
  · intro h v hv
    have he : 0 ≤ metricEnergy (a • (stepProjector s * W * stepProjector s) -
        stepProjector s * Z * stepProjector s) v := by
      simpa only [metricEnergy, dot, dotProduct, star_trivial] using h.2 v
    rw [EnergyIdentities.energy_sub_matrix, EnergyIdentities.energy_smul_matrix,
      projected_energy, projected_energy, stepProjector_fixes_perpendicular s v hv] at he
    linarith
  · intro h
    constructor
    · simp only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
        (stepProjector_isSymm s).eq, hW.eq, hZ.eq, Matrix.mul_assoc]
    · intro v
      have he : 0 ≤ metricEnergy (a • (stepProjector s * W * stepProjector s) -
          stepProjector s * Z * stepProjector s) v := by
        rw [EnergyIdentities.energy_sub_matrix, EnergyIdentities.energy_smul_matrix,
          projected_energy, projected_energy]
        exact sub_nonneg.mpr (h _ (stepProjector_perpendicular s v))
      simpa only [metricEnergy, dot, dotProduct, star_trivial] using he

/-- No nonzero or invertibility condition is imposed on ell. -/
theorem rank_one_transport {n : ℕ} (s v w : Vec n) (ell β a : ℝ)
    (hw : w = ell • v + β • s) (hell : ell ^ 2 ≤ a) :
    (a • (stepProjector s * outer v v * stepProjector s) -
      stepProjector s * outer w w * stepProjector s).PosSemidef := by
  have hp : (stepProjector s).mulVec w = ell • (stepProjector s).mulVec v := by
    rw [hw, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      stepProjector_mulVec_self, smul_zero, add_zero]
  rw [projected_outer, projected_outer, hp]
  have he : a • outer ((stepProjector s).mulVec v) ((stepProjector s).mulVec v) -
      outer (ell • (stepProjector s).mulVec v) (ell • (stepProjector s).mulVec v) =
      (a - ell ^ 2) • outer ((stepProjector s).mulVec v) ((stepProjector s).mulVec v) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, outer, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact SmoothSubspace.scaled_outer_posSemidef _ _ (sub_nonneg.mpr hell)

/-- Construct a PSD band certificate from the source's scalar comparison field. -/
def rankOneCertificate {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (v : Vec n → Vec n) (m C L δ : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hV : ∀ x ∈ positiveBand F K fstar η, ∀ g,
      HasFDerivAt F (gradientFunctional g) x → m ≤ (dot g (v x)) ^ 2)
    (hS : ∀ x z g h, x ∈ positiveBand F K fstar η →
      z ∈ positiveBand F K fstar η → EligiblePair F c₁ c₂ x z g h →
      pairDecrease x z g ≤ δ → (dot (h - g) (v z)) ^ 2 ≤ C * pairCurvature x z g h)
    (hT : ∀ x z g h, x ∈ positiveBand F K fstar η →
      z ∈ positiveBand F K fstar η → EligiblePair F c₁ c₂ x z g h →
      pairDecrease x z g ≤ δ → ∃ ell β : ℝ,
        v z = ell • v x + β • pairStep x z ∧ ell ^ 2 ≤ 1 + L * pairDecrease x z g) :
    BandCertificate F K fstar c₁ c₂ η where
  W x := outer (v x) (v x)
  m := m
  C := C
  L := L
  δ := δ
  m_pos := hm
  L_nonneg := hL
  delta_pos := hδ
  positive_semidefinite x _ _ := by
    simpa only [one_smul] using SmoothSubspace.scaled_outer_posSemidef (v x) 1 zero_le_one
  visibility x hx g hg := by
    rw [EnergyIdentities.energy_outer, show dot (v x) g = dot g (v x) from dotProduct_comm _ _]
    exact hV x hx g hg
  secant x z g h hx hz e hd := by
    rw [EnergyIdentities.energy_outer, show dot (v z) (h - g) = dot (h - g) (v z) from dotProduct_comm _ _]
    exact hS x z g h hx hz e hd
  transport x z g h hx hz e hd := by
    obtain ⟨ell, β, he, hell⟩ := hT x z g h hx hz e hd
    exact rank_one_transport _ _ _ ell β _ he hell

/-- RS implies the transported condition with the exact radial field,
visibility η² and L=0. No compactness or uniqueness is needed for this implication. -/
theorem radial_implies_band_certificates {n : ℕ} {F : Vec n → ℝ}
    {K : Set (Vec n)} (hF : ConvexOn ℝ univ F) (star : Vec n)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ < 1)
    (hRS : RadialCertificate.HasRadialSecantBounds F K star) :
    HasBandCertificates F K (F star) c₁ c₂ := by
  intro η hη _
  obtain ⟨C, hC⟩ := hRS η hη
  refine ⟨rankOneCertificate (fun x => x - star) (η ^ 2) C 0 1
    (sq_pos_of_pos hη) (le_refl _) zero_lt_one ?_ ?_ ?_⟩
  · intro x hx g hg
    have hs := convex_supporting_inequality hF hg star
    have he : dot g (star - x) = -dot g (x - star) := by
      unfold dot
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [he] at hs
    have hgap : η ≤ dot g (x - star) := by linarith [hx.2]
    nlinarith
  · intro x z g h hx hz e hd
    have hdec : F z ≤ F x := by
      have hp := mul_pos hc₁ e.decrease_pos
      linarith [e.armijo]
    exact hC x z g h hx.1 hz.1 hz.2 hdec e.gradient_x e.gradient_z
      (eligible_curvature_pos e hc₂)
  · intro x z g h hx hz e hd
    refine ⟨1, 1, ?_, ?_⟩
    · simp only [one_smul, pairStep]
      abel
    · simp


/-- Restrict the structural region; all numerical constants and the field are preserved. -/
def BandCertificate.restrict {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : BandCertificate F K fstar c₁ c₂ η)
    (K' : Set (Vec n)) (hsub : K' ⊆ K) : BandCertificate F K' fstar c₁ c₂ η where
  W := C.W
  m := C.m
  C := C.C
  L := C.L
  δ := C.δ
  m_pos := C.m_pos
  L_nonneg := C.L_nonneg
  delta_pos := C.delta_pos
  positive_semidefinite x hx hd := C.positive_semidefinite x ⟨hsub hx.1, hx.2⟩ hd
  visibility x hx g hg := C.visibility x ⟨hsub hx.1, hx.2⟩ g hg
  secant x z g h hx hz e hd := C.secant x z g h ⟨hsub hx.1, hx.2⟩ ⟨hsub hz.1, hz.2⟩ e hd
  transport x z g h hx hz e hd := C.transport x z g h ⟨hsub hx.1, hx.2⟩ ⟨hsub hz.1, hz.2⟩ e hd

theorem hasBandCertificates_restrict {n : ℕ} {F : Vec n → ℝ} {K K' : Set (Vec n)}
    {fstar c₁ c₂ : ℝ} (h : HasBandCertificates F K fstar c₁ c₂) (hsub : K' ⊆ K) :
    HasBandCertificates F K' fstar c₁ c₂ := by
  intro η hη hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨C⟩ := h η hη ⟨x, hsub hx.1, hx.2⟩
  exact ⟨C.restrict K' hsub⟩

/-- Certificates need only cover a one-sided level shell above each potential
positive limit, rather than an entire positive band. -/
def HasShellCertificates {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (fstar c₁ c₂ : ℝ) : Prop :=
  ∀ ell : ℝ, fstar < ell → (∃ x ∈ K, ell ≤ F x) →
    ∃ ε : ℝ, 0 < ε ∧
      Nonempty (BandCertificate F (K ∩ {x | F x ≤ ell + ε}) fstar c₁ c₂ (ell - fstar))

/-- A local basin valid for every admissible full-BFGS initial matrix. The
radius is selected before the run, using only the objective and neighborhood. -/
theorem local_transported_certificate_basin_on_neighborhood {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hunique : ∀ x, F x = F star → x = star) {U : Set (Vec n)} (hU : U ∈ 𝓝 star)
    {c₁ c₂ : ℝ} (hcert : HasBandCertificates F U (F star) c₁ c₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F,
      R.c₁ = c₁ → R.c₂ = c₂ → F (R.x 0) ≤ F star + δ →
      (∀ k, R.x k ∈ U) ∧
        Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨δ, hδ, hsub⟩ := Localization.neighborhood_basin hF star hmin hunique hU
  refine ⟨δ, hδ, ?_⟩
  intro R hc₁ hc₂ hstart
  have hc : HasBandCertificates F {x | F x ≤ F star + δ} (F star) R.c₁ R.c₂ := by
    rw [hc₁, hc₂]
    exact hasBandCertificates_restrict hcert hsub
  have hv := R.transported_certificate_values_on_sublevel (F star + δ)
    (Localization.sublevel_compact hF star hmin hunique _) star hmin hstart hc
  exact ⟨fun k => hsub ((R.objective_le_initial k).trans hstart), hv,
    R.iterates_tendsto_unique_min_of_values star hmin hunique hv⟩


/-- The source local statement only requires certificates on K∩U. Shrinking
the initial level keeps accepted iterates in both the original sublevel and U. -/
theorem local_transported_certificate_basin {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hunique : ∀ x, F x = F star → x = star) (b : ℝ) (hb : F star < b)
    {U : Set (Vec n)} (hU : U ∈ 𝓝 star) {c₁ c₂ : ℝ}
    (hcert : HasBandCertificates F ({x | F x ≤ b} ∩ U) (F star) c₁ c₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F,
      R.c₁ = c₁ → R.c₂ = c₂ → F (R.x 0) ≤ F star + δ →
      (∀ k, F (R.x k) ≤ b ∧ R.x k ∈ U) ∧
        Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧ Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨δ₀, hδ₀, hsub₀⟩ := Localization.neighborhood_basin hF star hmin hunique hU
  let δ := min δ₀ (b - F star)
  have hδ : 0 < δ := lt_min hδ₀ (sub_pos.mpr hb)
  have hsub : {x : Vec n | F x ≤ F star + δ} ⊆ {x | F x ≤ b} ∩ U := by
    intro x hx
    have hle₀ : δ ≤ δ₀ := min_le_left _ _
    have hleb : δ ≤ b - F star := min_le_right _ _
    constructor
    · change F x ≤ b
      change F x ≤ F star + δ at hx
      linarith
    · apply hsub₀
      change F x ≤ F star + δ at hx
      change F x ≤ F star + δ₀
      linarith
  refine ⟨δ, hδ, ?_⟩
  intro R hc₁ hc₂ hstart
  have hc : HasBandCertificates F {x | F x ≤ F star + δ} (F star) R.c₁ R.c₂ := by
    rw [hc₁, hc₂]
    exact hasBandCertificates_restrict hcert hsub
  have hv := R.transported_certificate_values_on_sublevel (F star + δ)
    (Localization.sublevel_compact hF star hmin hunique _) star hmin hstart hc
  exact ⟨fun k => hsub ((R.objective_le_initial k).trans hstart), hv,
    R.iterates_tendsto_unique_min_of_values star hmin hunique hv⟩

end TransportedCertificate

namespace AdmissibleBFGSRun
open TransportedCertificate

/-- The one-sided-shell version derives eventual membership from the actual
monotone value limit and derives eventual smallness from Armijo summability. -/
theorem transported_shell_certificate_values {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (K : Set (Vec n)) (hK : IsCompact K)
    (hxK : ∀ k, R.x k ∈ K) (star : Vec n) (hmin : ∀ x, F star ≤ F x)
    (hcert : HasShellCertificates F K (F star) R.c₁ R.c₂) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) := by
  have hsum := R.summable_predicted_decreases_of_lower_bound (F star) (fun k => hmin (R.x k))
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_set K hK hxK
  have hbounded : BddBelow (Set.range (fun k => F (R.x k))) := by
    refine ⟨F star, ?_⟩
    rintro z ⟨k, rfl⟩
    exact hmin _
  let ell := ⨅ k, F (R.x k)
  have hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ell) :=
    tendsto_atTop_ciInf R.objective_antitone hbounded
  have hfloor : F star ≤ ell := le_ciInf (fun k => hmin (R.x k))
  have hlevels : ∀ k, ell ≤ F (R.x k) := fun k => ciInf_le hbounded k
  have hvalue : ell = F star := by
    by_contra hne
    have hpos : F star < ell := lt_of_le_of_ne hfloor (Ne.symm hne)
    obtain ⟨ε, hε, ⟨C⟩⟩ := hcert ell hpos ⟨R.x 0, hxK 0, hlevels 0⟩
    have hevent : ∀ᶠ k in atTop, R.d k < C.δ ∧ F (R.x k) < ell + ε :=
      (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds C.delta_pos)).and
        (hlim.eventually (gt_mem_nhds (by linarith : ell < ell + ε)))
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
    have hband : ∀ k, R.x (J + k) ∈
        positiveBand F (K ∩ {x | F x ≤ ell + ε}) (F star) (ell - F star) := by
      intro k
      refine ⟨⟨hxK _, (hJ (J + k) (Nat.le_add_right J k)).2.le⟩, ?_⟩
      linarith [hlevels (J + k)]
    exact (R.shift J).band_certificate_incompatible C hband
      (fun k => (hJ (J + k) (Nat.le_add_right J k)).1.le)
      G hG (fun k => hg (J + k)) (R.shift_summable_d hsum J)
  simpa only [hvalue] using hlim

/-- Complete compact-sublevel conclusion under one-sided-shell certificates. -/
theorem transported_shell_certificate_convergence_on_sublevel {n : ℕ} {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (b : ℝ) (hK : IsCompact {x : Vec n | F x ≤ b})
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (hstart : F (R.x 0) ≤ b)
    (hcert : HasShellCertificates F {x | F x ≤ b} (F star) R.c₁ R.c₂) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      ((∀ x, F x = F star → x = star) → Tendsto R.x atTop (𝓝 star)) := by
  have hxK : ∀ k, R.x k ∈ {x | F x ≤ b} := fun k => (R.objective_le_initial k).trans hstart
  have hv := R.transported_shell_certificate_values _ hK hxK star hmin hcert
  exact ⟨hv, R.distance_to_argmin_of_values star hmin hK hxK hv,
    fun hu => R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

end AdmissibleBFGSRun
end BfgsVerification
