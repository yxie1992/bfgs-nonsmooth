import BfgsVerification.CertificateGeometry
import BfgsVerification.AffineProjection
import BfgsVerification.ConvexDifferentiability
import Mathlib.Data.ENNReal.Real

/-! Module G's exact visibility/suppression feasibility, without transport.
Incoming families and target sets are arbitrary. Extended nonnegative reals
retain infinite support capacities and empty predecessor sets. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Set Matrix Filter

namespace BfgsVerification.PointwiseFeasibility
open CertificateGeometry

def incomingPolar {n : ℕ} {β : Type*} (y : β → Vec n) (t : β → ℝ) : Set (Vec n) :=
  {v | ∀ j, |dot (y j) v| ≤ Real.sqrt (t j)}

/-- Literal extended-real supremum of visible descent over all admissible
comparison directions. No boundedness or attainment is built into it. -/
def descentCapacity {n : ℕ} {β : Type*} (h : Vec n) (y : β → Vec n) (t : β → ℝ) : ℝ≥0∞ :=
  ⨆ v : incomingPolar y t, ENNReal.ofReal |dot h v.val|

def UniformDirections {n : ℕ} {α : Type*} {β : α → Type*}
    (h : α → Vec n) (y : ∀ z, β z → Vec n) (t : ∀ z, β z → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ z, ∃ v ∈ incomingPolar (y z) (t z), r ≤ |dot (h z) v|

def UniformPSD {n : ℕ} {α : Type*} {β : α → Type*}
    (h : α → Vec n) (y : ∀ z, β z → Vec n) (t : ∀ z, β z → ℝ) : Prop :=
  ∃ W : α → Mat n, ∃ m C : ℝ, 0 < m ∧
    (∀ z, (W z).PosSemidef) ∧ (∀ z, m ≤ metricEnergy (W z) (h z)) ∧
    ∀ z j, metricEnergy (W z) (y z j) ≤ C * t z j

/-- A positive infimum of the actual extended supremum is equivalent to a
uniform positive real descent witness. Infinite capacities and empty target
families are covered by the complete-lattice operations. -/
theorem uniformDirections_iff_capacity {n : ℕ} {α : Type*} {β : α → Type*}
    (h : α → Vec n) (y : ∀ z, β z → Vec n) (t : ∀ z, β z → ℝ) :
    UniformDirections h y t ↔ 0 < ⨅ z, descentCapacity (h z) (y z) (t z) := by
  constructor
  · rintro ⟨r, hr, hv⟩
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
    apply hpos.trans_le
    apply le_iInf
    intro z
    obtain ⟨v, hv, he⟩ := hv z
    exact le_iSup_of_le ⟨v, hv⟩ (ENNReal.ofReal_le_ofReal he)
  · intro hpos
    obtain ⟨r, hr0, hr⟩ := exists_between hpos
    have hrfin : r ≠ ∞ := ne_top_of_lt hr
    have hrreal : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hrfin
    refine ⟨r.toReal, hrreal, ?_⟩
    intro z
    have hz : r < descentCapacity (h z) (y z) (t z) := hr.trans_le (iInf_le _ z)
    obtain ⟨v, hv⟩ := lt_iSup_iff.mp hz
    refine ⟨v.val, v.property, ?_⟩
    rw [← ENNReal.ofReal_toReal hrfin] at hv
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrreal.le).mp hv).le

/-- Any feasible finite PSD field gives uniform admissible directions.
Replacing C by max C 1 handles every real C, including zero, without a new
assumption and without excluding empty incoming families. -/
theorem uniformDirections_of_uniformPSD {n : ℕ} {α : Type*} {β : α → Type*}
    {h : α → Vec n} {y : ∀ z, β z → Vec n} {t : ∀ z, β z → ℝ}
    (ht : ∀ z j, 0 ≤ t z j) (hPSD : UniformPSD h y t) : UniformDirections h y t := by
  obtain ⟨W, m, C, hm, hW, hV, hS⟩ := hPSD
  let D := max C 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  let r := (Real.sqrt D)⁻¹ * Real.sqrt m
  have hr : 0 < r := mul_pos (inv_pos.mpr hsD) (Real.sqrt_pos.mpr hm)
  refine ⟨r, hr, ?_⟩
  intro z
  obtain ⟨u, hu, huEq⟩ := ellipsoid_support_attained (hW z) (h z)
  refine ⟨(Real.sqrt D)⁻¹ • u, ?_, ?_⟩
  · intro j
    have hsec : metricEnergy (W z) (y z j) ≤ D * t z j :=
      (hS z j).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (ht z j))
    have hb := (ellipsoid_suppression_iff (hW z) (y z j) (D * t z j)).mp hsec |>.2 u hu
    rw [Real.sqrt_mul hD.le] at hb
    rw [dot_smul_right, abs_mul, abs_of_nonneg (inv_nonneg.mpr hsD.le)]
    calc
      _ ≤ (Real.sqrt D)⁻¹ * (Real.sqrt D * Real.sqrt (t z j)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hsD.le)
      _ = Real.sqrt (t z j) := by rw [← mul_assoc, inv_mul_cancel₀ hsD.ne', one_mul]
  · rw [dot_smul_right, huEq, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hsD.le) (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hV z)) (inv_nonneg.mpr hsD.le)

/-- Pointwise choices yield an explicit rank-one field with suppression
constant one. No continuity or boundedness of these choices is imposed. -/
theorem rankOne_of_uniformDirections {n : ℕ} {α : Type*} {β : α → Type*}
    {h : α → Vec n} {y : ∀ z, β z → Vec n} {t : ∀ z, β z → ℝ}
    (ht : ∀ z j, 0 ≤ t z j) (hd : UniformDirections h y t) :
    ∃ v : α → Vec n, ∃ m : ℝ, 0 < m ∧
      (∀ z, (outer (v z) (v z)).PosSemidef) ∧
      (∀ z, m ≤ metricEnergy (outer (v z) (v z)) (h z)) ∧
      ∀ z j, metricEnergy (outer (v z) (v z)) (y z j) ≤ t z j := by
  obtain ⟨r, hr, hd⟩ := hd
  choose v hv hvis using hd
  refine ⟨v, r ^ 2, sq_pos_of_pos hr, ?_, ?_, ?_⟩
  · intro z
    simpa only [one_smul] using SmoothSubspace.scaled_outer_posSemidef (v z) 1 zero_le_one
  · intro z
    rw [EnergyIdentities.energy_outer]
    have hh : r ≤ |dot (v z) (h z)| := by
      rw [show dot (v z) (h z) = dot (h z) (v z) from dotProduct_comm _ _]
      exact hvis z
    nlinarith [sq_abs (dot (v z) (h z))]
  · intro z j
    rw [EnergyIdentities.energy_outer]
    have hh : |dot (v z) (y z j)| ≤ Real.sqrt (t z j) := by
      rw [show dot (v z) (y z j) = dot (y z j) (v z) from dotProduct_comm _ _]
      exact hv z j
    nlinarith [sq_abs (dot (v z) (y z j)), Real.sq_sqrt (ht z j), abs_nonneg (dot (v z) (y z j))]

/-- Literal source feasibility criterion: a finite-valued PSD field with
uniform (V),(S) constants exists exactly when inf_z nu(z)>0. Higher rank adds
no pointwise feasibility power. This theorem makes no transport assertion. -/
theorem uniformPSD_iff_capacity {n : ℕ} {α : Type*} {β : α → Type*}
    (h : α → Vec n) (y : ∀ z, β z → Vec n) (t : ∀ z, β z → ℝ)
    (ht : ∀ z j, 0 ≤ t z j) :
    UniformPSD h y t ↔ 0 < ⨅ z, descentCapacity (h z) (y z) (t z) := by
  constructor
  · intro hPSD
    exact (uniformDirections_iff_capacity h y t).mp (uniformDirections_of_uniformPSD ht hPSD)
  · intro hc
    obtain ⟨v, m, hm, hW, hV, hS⟩ := rankOne_of_uniformDirections ht
      ((uniformDirections_iff_capacity h y t).mpr hc)
    exact ⟨fun z => outer (v z) (v z), m, 1, hm, hW, hV, by simpa only [one_mul] using hS⟩

open TransportedCertificate

/-- Source differentiable endpoints in the exact objective band. -/
def BandPoint {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (fstar η : ℝ) :=
  {z : Vec n // z ∈ positiveBand F K fstar η ∧ DifferentiableAt ℝ F z}

/-- Every source predecessor, at the fixed threshold. There is no finite
sampling or common-trajectory restriction on this type. -/
def IncomingPoint {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (fstar c₁ c₂ η δ : ℝ)
    (z : BandPoint F K fstar η) :=
  {x : BandPoint F K fstar η //
    EligiblePair F c₁ c₂ x.val z.val (coordinateGradient F x.val) (coordinateGradient F z.val) ∧
    pairDecrease x.val z.val (coordinateGradient F x.val) ≤ δ}

def sourceJump {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η δ : ℝ}
    (z : BandPoint F K fstar η) (x : IncomingPoint F K fstar c₁ c₂ η δ z) : Vec n :=
  coordinateGradient F z.val - coordinateGradient F x.val.val

def sourceCurvature {n : ℕ} {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η δ : ℝ}
    (z : BandPoint F K fstar η) (x : IncomingPoint F K fstar c₁ c₂ η δ z) : ℝ :=
  pairCurvature x.val.val z.val (coordinateGradient F x.val.val) (coordinateGradient F z.val)

/-- Module G's nu on its exact continuum of eligible incoming objective pairs. -/
def sourceCapacity {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n)) (fstar c₁ c₂ η δ : ℝ)
    (z : BandPoint F K fstar η) : ℝ≥0∞ :=
  descentCapacity (coordinateGradient F z.val)
    (sourceJump (c₁ := c₁) (c₂ := c₂) (δ := δ) z) (sourceCurvature z)

theorem coordinateGradient_eq {n : ℕ} {F : Vec n → ℝ} {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) : coordinateGradient F x = g :=
  AffineProjection.gradientFunctional_injective
    ((hasFDerivAt_coordinateGradient hg.differentiableAt).unique hg)

theorem source_uniformPSD_iff {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (fstar c₁ c₂ η δ : ℝ) (hδ : 0 < δ) :
    UniformPSD (fun z : BandPoint F K fstar η => coordinateGradient F z.val)
      (sourceJump (c₁ := c₁) (c₂ := c₂) (δ := δ)) sourceCurvature ↔
      ∃ B : VisibilitySecantCertificate F K fstar c₁ c₂ η, B.δ = δ := by
  classical
  constructor
  · rintro ⟨W, m, C, hm, hW, hV, hS⟩
    let field : Vec n → Mat n := fun x =>
      if hx : x ∈ positiveBand F K fstar η ∧ DifferentiableAt ℝ F x then W ⟨x, hx⟩ else 0
    have field_eq (x : Vec n) (hx : x ∈ positiveBand F K fstar η ∧ DifferentiableAt ℝ F x) :
        field x = W ⟨x, hx⟩ := dif_pos hx
    refine ⟨{
      W := field
      m := m
      C := C
      δ := δ
      m_pos := hm
      delta_pos := hδ
      positive_semidefinite := ?_
      visibility := ?_
      secant := ?_ }, rfl⟩
    · intro x hx hd
      rw [field_eq x ⟨hx, hd⟩]
      exact hW ⟨x, hx, hd⟩
    · intro x hx g hg
      rw [field_eq x ⟨hx, hg.differentiableAt⟩]
      simpa only [coordinateGradient_eq hg] using hV ⟨x, hx, hg.differentiableAt⟩
    · intro x z g h hx hz hp hd
      have hgEq := coordinateGradient_eq hp.gradient_x
      have hhEq := coordinateGradient_eq hp.gradient_z
      let zp : BandPoint F K fstar η := ⟨z, hz, hp.gradient_z.differentiableAt⟩
      let xp : IncomingPoint F K fstar c₁ c₂ η δ zp :=
        ⟨⟨x, hx, hp.gradient_x.differentiableAt⟩, by simpa only [zp, hgEq, hhEq] using hp,
          by simpa only [hgEq] using hd⟩
      rw [field_eq z ⟨hz, hp.gradient_z.differentiableAt⟩]
      simpa only [sourceJump, sourceCurvature, zp, xp, hgEq, hhEq] using hS zp xp
  · rintro ⟨B, hBδ⟩
    refine ⟨fun z => B.W z.val, B.m, B.C, B.m_pos, ?_, ?_, ?_⟩
    · intro z
      exact B.positive_semidefinite z.val z.property.1 z.property.2
    · intro z
      exact B.visibility z.val z.property.1 _ (hasFDerivAt_coordinateGradient z.property.2)
    · intro z x
      exact B.secant x.val.val z.val _ _ x.val.property.1 z.property.1 x.property.1
        (by simpa only [hBδ] using x.property.2)

/-- Exact source fixed-threshold criterion, with every eligible predecessor
and actual derivatives. Existence of (V),(S) alone is equivalent to the strict
positivity of the extended-real infimum of nu. -/
theorem visibility_secant_iff_source_capacity {n : ℕ} (F : Vec n → ℝ) (K : Set (Vec n))
    (fstar c₁ c₂ η δ : ℝ) (hc₂ : c₂ < 1) (hδ : 0 < δ) :
    (∃ B : VisibilitySecantCertificate F K fstar c₁ c₂ η, B.δ = δ) ↔
      0 < ⨅ z, sourceCapacity F K fstar c₁ c₂ η δ z := by
  rw [← source_uniformPSD_iff F K fstar c₁ c₂ η δ hδ]
  apply uniformPSD_iff_capacity
  intro z x
  exact ((mul_pos (sub_pos.mpr hc₂) x.property.1.decrease_pos).trans_le x.property.1.curvature).le

end BfgsVerification.PointwiseFeasibility
