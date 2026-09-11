import BfgsVerification.TransportedCertificateAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Module G's exact elimination of the linear transport budget.  The field is
rescaled pointwise; neither it nor its derivatives are assumed bounded. -/
noncomputable section
open Matrix

namespace BfgsVerification
namespace TransportedCertificate

theorem psd_smul {n : ℕ} {A : Mat n} (hA : A.PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    (a • A).PosSemidef := by
  constructor
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial]
      using congrArg (fun B : Mat n => a • B) hA.isHermitian
  · intro x
    have he : 0 ≤ metricEnergy A x := by
      simpa only [metricEnergy, dot, dotProduct, star_trivial] using hA.2 x
    simpa only [metricEnergy, dot, dotProduct, star_trivial] using
      (show 0 ≤ metricEnergy (a • A) x by
        rw [EnergyIdentities.energy_smul_matrix]; exact mul_nonneg ha he)

theorem projected_psd {n : ℕ} {W : Mat n} (hW : W.PosSemidef) (s : Vec n) :
    (stepProjector s * W * stepProjector s).PosSemidef := by
  have h := hW.mul_mul_conjTranspose_same (stepProjector s)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    (stepProjector_isSymm s).eq] using h

/-- Scale a Loewner comparison, permitting a larger target multiplier. -/
theorem scale_loewner {n : ℕ} {X Z : Mat n} (hX : X.PosSemidef)
    {a u v : ℝ} (hu : 0 ≤ u) (hT : (a • X - Z).PosSemidef)
    (huv : u * a ≤ v) : (v • X - u • Z).PosSemidef := by
  have h := (psd_smul hT hu).add (psd_smul hX (sub_nonneg.mpr huv))
  convert h using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eligible_curvature_pos {n : ℕ} {F : Vec n → ℝ} {c₁ c₂ : ℝ}
    {x z g h : Vec n} (e : EligiblePair F c₁ c₂ x z g h) (hc₂ : c₂ < 1) :
    0 < pairCurvature x z g h :=
  (mul_pos (sub_pos.mpr hc₂) e.decrease_pos).trans_le e.curvature

/-- Bounded positive pointwise rescaling. The scalar condition is exactly what
is needed after multiplying the old projected inequality. -/
def BandCertificate.rescale {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : BandCertificate F K fstar c₁ c₂ η)
    (hc₂ : c₂ < 1) (w : Vec n → ℝ) (lo hi L' : ℝ)
    (hlo : 0 < lo) (hL' : 0 ≤ L')
    (hw : ∀ x ∈ positiveBand F K fstar η, lo ≤ w x ∧ w x ≤ hi)
    (hscale : ∀ x z g h, x ∈ positiveBand F K fstar η →
      z ∈ positiveBand F K fstar η → EligiblePair F c₁ c₂ x z g h →
      pairDecrease x z g ≤ C.δ →
      w z * (1 + C.L * pairDecrease x z g) ≤ (1 + L' * pairDecrease x z g) * w x) :
    BandCertificate F K fstar c₁ c₂ η where
  W x := w x • C.W x
  m := lo * C.m
  C := hi * max C.C 0
  L := L'
  δ := C.δ
  m_pos := mul_pos hlo C.m_pos
  L_nonneg := hL'
  delta_pos := C.delta_pos
  positive_semidefinite x hx hd := psd_smul (C.positive_semidefinite x hx hd)
    (hlo.le.trans (hw x hx).1)
  visibility x hx g hg := by
    rw [EnergyIdentities.energy_smul_matrix]
    exact mul_le_mul (hw x hx).1 (C.visibility x hx g hg) C.m_pos.le
      (hlo.le.trans (hw x hx).1)
  secant x z g h hx hz e hd := by
    rw [EnergyIdentities.energy_smul_matrix]
    have ht := (eligible_curvature_pos e hc₂).le
    have hsec := (C.secant x z g h hx hz e hd).trans
      (mul_le_mul_of_nonneg_right (le_max_left C.C 0) ht)
    calc
      w z * metricEnergy (C.W z) (h - g) ≤ w z * (max C.C 0 * pairCurvature x z g h) :=
        mul_le_mul_of_nonneg_left hsec (hlo.le.trans (hw z hz).1)
      _ ≤ hi * (max C.C 0 * pairCurvature x z g h) :=
        mul_le_mul_of_nonneg_right (hw z hz).2 (mul_nonneg (le_max_right _ _) ht)
      _ = _ := by ring
  transport x z g h hx hz e hd := by
    have h := scale_loewner (projected_psd
      (C.positive_semidefinite x hx e.gradient_x.differentiableAt) (pairStep x z))
      (hlo.le.trans (hw z hz).1) (C.transport x z g h hx hz e hd)
      (hscale x z g h hx hz e hd)
    simpa only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] using h

/-- Armijo absorbs the complete old linear budget into an exponential value
weight. This is an exact inequality, with the original small-pair threshold. -/
theorem value_weight_transport {L c₁ d fx fz fstar : ℝ}
    (hL : 0 ≤ L) (hc₁ : 0 < c₁) (hA : c₁ * d ≤ fx - fz) :
    Real.exp ((L / c₁) * (fz - fstar)) * (1 + L * d) ≤
      Real.exp ((L / c₁) * (fx - fstar)) := by
  have hk : 0 ≤ L / c₁ := div_nonneg hL hc₁.le
  have hscaled := mul_le_mul_of_nonneg_left hA hk
  have hcancel : L / c₁ * c₁ = L := div_mul_cancel₀ L hc₁.ne'
  rw [← mul_assoc, hcancel] at hscaled
  calc
    _ ≤ Real.exp ((L / c₁) * (fz - fstar)) * Real.exp (L * d) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [add_comm] using Real.add_one_le_exp (L * d)
    _ = Real.exp ((L / c₁) * (fz - fstar) + L * d) := (Real.exp_add _ _).symm
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith

/-- Module G normalization with exactly Ŵ(x)=exp((L/c₁)(F(x)-F*)) W(x). -/
def BandCertificate.normalize {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : BandCertificate F K fstar c₁ c₂ η)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (b : ℝ)
    (hb : ∀ x ∈ positiveBand F K fstar η, F x ≤ b) :
    BandCertificate F K fstar c₁ c₂ η :=
  C.rescale hc₂ (fun x => Real.exp ((C.L / c₁) * (F x - fstar)))
    (Real.exp ((C.L / c₁) * η)) (Real.exp ((C.L / c₁) * (b - fstar))) 0
    (Real.exp_pos _) (le_refl _) (by
      intro x hx
      have hk : 0 ≤ C.L / c₁ := div_nonneg C.L_nonneg hc₁.le
      constructor <;> apply Real.exp_le_exp.mpr
      · exact mul_le_mul_of_nonneg_left (by linarith [hx.2]) hk
      · exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hb x hx) fstar) hk)
    (by
      intro x z g h hx hz e hd
      simpa only [zero_mul, add_zero, one_mul] using
        value_weight_transport C.L_nonneg hc₁ e.armijo)

theorem BandCertificate.normalize_field {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : BandCertificate F K fstar c₁ c₂ η)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (b : ℝ)
    (hb : ∀ x ∈ positiveBand F K fstar η, F x ≤ b) (x : Vec n) :
    (C.normalize hc₁ hc₂ b hb).W x =
      Real.exp ((C.L / c₁) * (F x - fstar)) • C.W x := rfl

theorem BandCertificate.normalize_budget {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : BandCertificate F K fstar c₁ c₂ η)
    (hc₁ : 0 < c₁) (hc₂ : c₂ < 1) (b : ℝ)
    (hb : ∀ x ∈ positiveBand F K fstar η, F x ≤ b) :
    (C.normalize hc₁ hc₂ b hb).L = 0 ∧ (C.normalize hc₁ hc₂ b hb).δ = C.δ := ⟨rfl, rfl⟩

/-- Existence of transported certificates is equivalent to existence with
exact nonexpansion; no uniform field bound has been introduced. -/
theorem hasBandCertificates_iff_zero_budget {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : c₂ < 1)
    (b : ℝ) (hb : ∀ x ∈ K, F x ≤ b) :
    HasBandCertificates F K fstar c₁ c₂ ↔
      ∀ η : ℝ, 0 < η → (positiveBand F K fstar η).Nonempty →
        ∃ C : BandCertificate F K fstar c₁ c₂ η, C.L = 0 := by
  constructor
  · intro h η hη hne
    obtain ⟨C⟩ := h η hη hne
    exact ⟨C.normalize hc₁ hc₂ b (fun x hx => hb x hx.1), rfl⟩
  · intro h η hη hne
    obtain ⟨C, _⟩ := h η hη hne
    exact ⟨C⟩


/-- Source variant with an arbitrary bounded potential. This places no
regularity or rank condition on the field or potential. -/
structure PotentialBandCertificate {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (fstar c₁ c₂ η : ℝ) where
  W : Vec n → Mat n
  Ψ : Vec n → ℝ
  m : ℝ
  C : ℝ
  L : ℝ
  δ : ℝ
  ψlo : ℝ
  ψhi : ℝ
  m_pos : 0 < m
  L_nonneg : 0 ≤ L
  delta_pos : 0 < δ
  potential_bounds : ∀ x ∈ positiveBand F K fstar η, ψlo ≤ Ψ x ∧ Ψ x ≤ ψhi
  positive_semidefinite : ∀ x ∈ positiveBand F K fstar η,
    DifferentiableAt ℝ F x → (W x).PosSemidef
  visibility : ∀ x ∈ positiveBand F K fstar η, ∀ g,
    HasFDerivAt F (gradientFunctional g) x → m ≤ metricEnergy (W x) g
  secant : ∀ x z g h, x ∈ positiveBand F K fstar η →
    z ∈ positiveBand F K fstar η → EligiblePair F c₁ c₂ x z g h →
    pairDecrease x z g ≤ δ → metricEnergy (W z) (h - g) ≤ C * pairCurvature x z g h
  transport : ∀ x z g h, x ∈ positiveBand F K fstar η →
    z ∈ positiveBand F K fstar η → EligiblePair F c₁ c₂ x z g h →
    pairDecrease x z g ≤ δ →
    (Real.exp (L * pairDecrease x z g + Ψ x - Ψ z) •
      (stepProjector (pairStep x z) * W x * stepProjector (pairStep x z)) -
      stepProjector (pairStep x z) * W z * stepProjector (pairStep x z)).PosSemidef

/-- A concrete small-decrease threshold and linear exponential bound. -/
theorem exp_small_linear {L d : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hsmall : d ≤ (L + 1)⁻¹) : Real.exp (L * d) ≤ 1 + (2 * L) * d := by
  have hp : 0 < L + 1 := by linarith
  have hprod : (L + 1) * d ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsmall hp.le
    simpa only [mul_inv_cancel₀ hp.ne'] using hh
  have hb : |L * d| ≤ 1 := by rw [abs_of_nonneg (mul_nonneg hL hd)]; nlinarith
  have he := (le_abs_self (Real.exp (L * d) - 1)).trans (Real.abs_exp_sub_one_le hb)
  rw [abs_of_nonneg (mul_nonneg hL hd)] at he
  linarith

def PotentialBandCertificate.absorb {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : PotentialBandCertificate F K fstar c₁ c₂ η)
    (hc₂ : c₂ < 1) : BandCertificate F K fstar c₁ c₂ η where
  W x := Real.exp (C.Ψ x) • C.W x
  m := Real.exp C.ψlo * C.m
  C := Real.exp C.ψhi * max C.C 0
  L := 2 * C.L
  δ := min C.δ (C.L + 1)⁻¹
  m_pos := mul_pos (Real.exp_pos _) C.m_pos
  L_nonneg := mul_nonneg (by norm_num) C.L_nonneg
  delta_pos := lt_min C.delta_pos (inv_pos.mpr (by linarith [C.L_nonneg]))
  positive_semidefinite x hx hd := psd_smul (C.positive_semidefinite x hx hd) (Real.exp_pos _).le
  visibility x hx g hg := by
    rw [EnergyIdentities.energy_smul_matrix]
    exact mul_le_mul (Real.exp_le_exp.mpr (C.potential_bounds x hx).1)
      (C.visibility x hx g hg) C.m_pos.le (Real.exp_pos _).le
  secant x z g h hx hz e hd := by
    rw [EnergyIdentities.energy_smul_matrix]
    have ht := (eligible_curvature_pos e hc₂).le
    have hsec := (C.secant x z g h hx hz e (hd.trans (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_right (le_max_left C.C 0) ht)
    calc
      Real.exp (C.Ψ z) * metricEnergy (C.W z) (h - g) ≤
          Real.exp (C.Ψ z) * (max C.C 0 * pairCurvature x z g h) :=
        mul_le_mul_of_nonneg_left hsec (Real.exp_pos _).le
      _ ≤ Real.exp C.ψhi * (max C.C 0 * pairCurvature x z g h) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (C.potential_bounds z hz).2)
          (mul_nonneg (le_max_right _ _) ht)
      _ = _ := by ring
  transport x z g h hx hz e hd := by
    have hs : Real.exp (C.Ψ z) * Real.exp (C.L * pairDecrease x z g + C.Ψ x - C.Ψ z) ≤
        (1 + (2 * C.L) * pairDecrease x z g) * Real.exp (C.Ψ x) := by
      calc
        _ = Real.exp (C.L * pairDecrease x z g) * Real.exp (C.Ψ x) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (exp_small_linear C.L_nonneg e.decrease_pos.le (hd.trans (min_le_right _ _)))
          (Real.exp_pos _).le
    have ht := scale_loewner (projected_psd
      (C.positive_semidefinite x hx e.gradient_x.differentiableAt) (pairStep x z))
      (Real.exp_pos (C.Ψ z)).le
      (C.transport x z g h hx hz e (hd.trans (min_le_left _ _))) hs
    simpa only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] using ht

theorem PotentialBandCertificate.absorb_field {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : PotentialBandCertificate F K fstar c₁ c₂ η)
    (hc₂ : c₂ < 1) (x : Vec n) :
    (C.absorb hc₂).W x = Real.exp (C.Ψ x) • C.W x := rfl

theorem PotentialBandCertificate.absorb_constants {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)}
    {fstar c₁ c₂ η : ℝ} (C : PotentialBandCertificate F K fstar c₁ c₂ η)
    (hc₂ : c₂ < 1) :
    (C.absorb hc₂).L = 2 * C.L ∧ (C.absorb hc₂).δ = min C.δ (C.L + 1)⁻¹ := ⟨rfl, rfl⟩

end TransportedCertificate
end BfgsVerification
