import BfgsVerification.CertificateGeometry
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Module G's tangent/normal interpretation, with its necessary qualifications.
The limiting annihilation results explicitly require convergence of the field
values, as supplied by a finite continuous extension; arbitrary fields are not
silently assumed to have that regularity. -/

noncomputable section
open scoped BigOperators Topology
open Set Matrix Filter

namespace BfgsVerification.AccessibleJumpGeometry
open CertificateGeometry

/-- Exactly the span of all differences between active gradient vectors. -/
def jumpSpace {n : ℕ} {α : Type*} (g : α → EuclideanSpace ℝ (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) := vectorSpan ℝ (Set.range g)

def tangentSpace {n : ℕ} {α : Type*} (g : α → EuclideanSpace ℝ (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (jumpSpace g)ᗮ

/-- Every active first-order model has the same tangential component.
The index family need not be finite. -/
theorem common_tangential_projection {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i j : α) :
    (tangentSpace g).orthogonalProjection (g i) =
      (tangentSpace g).orthogonalProjection (g j) := by
  apply sub_eq_zero.mp
  rw [← map_sub, Submodule.orthogonalProjection_eq_zero_iff]
  change g i - g j ∈ (jumpSpace g)ᗮᗮ
  rw [Submodule.orthogonal_orthogonal]
  exact vsub_mem_vectorSpan ℝ (Set.mem_range_self i) (Set.mem_range_self j)

/-- The algebraic nonstationarity distinction in the source is exact:
vanishing common tangent gradient is equivalent to zero in the affine hull,
which is not asserted to equal the convex hull. -/
theorem tangent_projection_zero_iff_zero_mem_affineSpan {n : ℕ} {α : Type*}
    (g : α → EuclideanSpace ℝ (Fin n)) (i : α) :
    (tangentSpace g).orthogonalProjection (g i) = 0 ↔
      (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (Set.range g) := by
  rw [Submodule.orthogonalProjection_eq_zero_iff]
  change g i ∈ (jumpSpace g)ᗮᗮ ↔ _
  rw [Submodule.orthogonal_orthogonal]
  constructor
  · intro h
    exact (mem_affineSpan_iff_exists ℝ).mpr
      ⟨g i, Set.mem_range_self i, -(g i), (jumpSpace g).neg_mem h, by simp⟩
  · intro h
    have hv := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan h
      (mem_affineSpan ℝ (Set.mem_range_self i))
    simpa only [vsub_eq_sub, zero_sub, Submodule.neg_mem_iff] using hv

/-- Annihilating the accessible jumps annihilates their entire linear span. -/
theorem jumpSpace_le_kernel {n : ℕ} {α : Type*} (W : Mat n) (g : α → Vec n)
    (hann : ∀ i j, W.mulVec (g i - g j) = 0) :
    jumpSpace (fun i => euclideanVector (g i)) ≤ LinearMap.ker (Matrix.toEuclideanLin W) := by
  unfold jumpSpace
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro v ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
  change Matrix.toEuclideanLin W (euclideanVector (g i) - euclideanVector (g j)) = 0
  ext k
  change (W.mulVec (g i - g j)) k = 0
  rw [hann]
  rfl

/-- For a symmetric field value annihilating the jump span, its actual range
is tangential to that span. No finite active-gradient family is required. -/
theorem range_tangential_of_annihilates {n : ℕ} {α : Type*} (W : Mat n)
    (hW : W.IsSymm) (g : α → Vec n) (hann : ∀ i j, W.mulVec (g i - g j) = 0)
    {v : Vec n} (hv : v ∈ matrixRange W) :
    euclideanVector v ∈ tangentSpace (fun i => euclideanVector (g i)) := by
  obtain ⟨u, rfl⟩ := hv
  apply (Submodule.mem_orthogonal _ _).mpr
  intro a ha
  have hz := jumpSpace_le_kernel W g hann ha
  have hza : W.mulVec (fun i => a i) = 0 := by
    ext i
    exact congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hz
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change dot (W.mulVec u) (fun i => a i) = 0
  rw [show dot (W.mulVec u) (fun i => a i) = dot (fun i => a i) (W.mulVec u) from dotProduct_comm _ _]
  rw [CertificateGeometry.dot_mulVec, hW.eq, hza]
  simp [dot]

/-- Exact accessibility-qualified range statement: only the span of jumps
actually annihilated by the limiting field is removed. This does not identify
that span with all active-gradient differences without a spanning proof. -/
theorem range_orthogonal_to_accessible_jumps {n : ℕ} {α : Type*} (W : Mat n)
    (hW : W.IsSymm) (jump : α → Vec n) (hann : ∀ i, W.mulVec (jump i) = 0)
    {v : Vec n} (hv : v ∈ matrixRange W) :
    euclideanVector v ∈ (Submodule.span ℝ (Set.range (fun i => euclideanVector (jump i))))ᗮ := by
  have hk : Submodule.span ℝ (Set.range (fun i => euclideanVector (jump i))) ≤
      LinearMap.ker (Matrix.toEuclideanLin W) := by
    apply Submodule.span_le.mpr
    rintro a ⟨i, rfl⟩
    change Matrix.toEuclideanLin W (euclideanVector (jump i)) = 0
    ext k
    change (W.mulVec (jump i)) k = 0
    rw [hann]
    rfl
  obtain ⟨u, rfl⟩ := hv
  apply (Submodule.mem_orthogonal _ _).mpr
  intro a ha
  have hz := hk ha
  have hza : W.mulVec (fun i => a i) = 0 := by
    ext i
    exact congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hz
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change dot (W.mulVec u) (fun i => a i) = 0
  rw [show dot (W.mulVec u) (fun i => a i) = dot (fun i => a i) (W.mulVec u) from dotProduct_comm _ _]
  rw [CertificateGeometry.dot_mulVec, hW.eq, hza]
  simp [dot]

/-- Visibility always leaves a nonzero component orthogonal to the accessible
jump span. No assumption identifies accessible and all active jumps. -/
theorem visible_accessible_projection_ne_zero {n : ℕ} {α : Type*} (W : Mat n)
    (jump : α → Vec n) (hann : ∀ i, W.mulVec (jump i) = 0) (g : Vec n)
    (hV : 0 < metricEnergy W g) :
    (Submodule.span ℝ (Set.range (fun i => euclideanVector (jump i))))ᗮ.orthogonalProjection
      (euclideanVector g) ≠ 0 := by
  intro hz
  have hm := (Submodule.orthogonalProjection_eq_zero_iff).mp hz
  rw [Submodule.orthogonal_orthogonal] at hm
  have hk : Submodule.span ℝ (Set.range (fun i => euclideanVector (jump i))) ≤
      LinearMap.ker (Matrix.toEuclideanLin W) := by
    apply Submodule.span_le.mpr
    rintro a ⟨i, rfl⟩
    change Matrix.toEuclideanLin W (euclideanVector (jump i)) = 0
    ext k
    change (W.mulVec (jump i)) k = 0
    rw [hann]
    rfl
  have hw := hk hm
  have hzero : W.mulVec g = 0 := by
    ext k
    exact congrArg (fun z : EuclideanSpace ℝ (Fin n) => z k) hw
  have he : metricEnergy W g = 0 := by simp [metricEnergy, hzero, dot]
  linarith

/-- Visibility rules out a zero common tangential component once the actual
limiting field annihilates all accessible active-gradient differences. -/
theorem visible_tangent_projection_ne_zero {n : ℕ} {α : Type*} (W : Mat n)
    (g : α → Vec n) (hann : ∀ i j, W.mulVec (g i - g j) = 0)
    (i : α) (hV : 0 < metricEnergy W (g i)) :
    (tangentSpace (fun j => euclideanVector (g j))).orthogonalProjection
      (euclideanVector (g i)) ≠ 0 := by
  intro hz
  have hm := (Submodule.orthogonalProjection_eq_zero_iff).mp hz
  change euclideanVector (g i) ∈ (jumpSpace (fun j => euclideanVector (g j)))ᗮᗮ at hm
  rw [Submodule.orthogonal_orthogonal] at hm
  have hw := jumpSpace_le_kernel W g hann hm
  have hzero : W.mulVec (g i) = 0 := by
    ext k
    exact congrArg (fun z : EuclideanSpace ℝ (Fin n) => z k) hw
  have he : metricEnergy W (g i) = 0 := by simp [metricEnergy, hzero, dot]
  linarith

theorem continuous_metricEnergy {n : ℕ} :
    Continuous (fun p : Mat n × Vec n => metricEnergy p.1 p.2) := by
  unfold metricEnergy dot Matrix.mulVec dotProduct
  fun_prop

/-- The PSD cone is closed under an actual matrix limit, derived directly
from finite matrix symmetry and every quadratic test. -/
theorem posSemidef_limit {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {W : ι → Mat n} {W₀ : Mat n} (hlim : Tendsto W l (𝓝 W₀))
    (hW : ∀ᶠ a in l, (W a).PosSemidef) : W₀.PosSemidef := by
  have hsym : ∀ᶠ a in l, (W a)ᵀ = W a := hW.mono (fun a ha => by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using ha.isHermitian)
  have ht : Tendsto (fun a => (W a)ᵀ) l (𝓝 W₀ᵀ) :=
    (continuous_id.matrix_transpose.tendsto W₀).comp hlim
  refine ⟨?_, ?_⟩
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      tendsto_nhds_unique_of_eventuallyEq ht hlim hsym
  · intro v
    have he : Tendsto (fun a => metricEnergy (W a) v) l (𝓝 (metricEnergy W₀ v)) :=
      continuous_metricEnergy.continuousAt.tendsto.comp (hlim.prodMk_nhds tendsto_const_nhds)
    have hp : ∀ᶠ a in l, 0 ≤ metricEnergy (W a) v := hW.mono (fun a ha => by
      simpa only [metricEnergy, dot, star_trivial] using ha.2 v)
    simpa only [metricEnergy, dot, star_trivial] using ge_of_tendsto he hp

/-- Vanishing incoming curvature forces the limiting field to annihilate the
limiting jump only under the explicitly supplied field-value convergence. -/
theorem suppression_limit_annihilates {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {W : ι → Mat n} {W₀ : Mat n} {y : ι → Vec n} {y₀ : Vec n} {t : ι → ℝ}
    (hWlim : Tendsto W l (𝓝 W₀)) (hylim : Tendsto y l (𝓝 y₀))
    (htlim : Tendsto t l (𝓝 0)) (hW : ∀ᶠ a in l, (W a).PosSemidef)
    (C : ℝ) (hS : ∀ᶠ a in l, metricEnergy (W a) (y a) ≤ C * t a) :
    W₀.mulVec y₀ = 0 := by
  have hPSD := posSemidef_limit hWlim hW
  have he : Tendsto (fun a => metricEnergy (W a) (y a)) l (𝓝 (metricEnergy W₀ y₀)) :=
    continuous_metricEnergy.continuousAt.tendsto.comp (hWlim.prodMk_nhds hylim)
  have hc : Tendsto (fun a => C * t a) l (𝓝 0) := by simpa only [mul_zero] using htlim.const_mul C
  have hle : metricEnergy W₀ y₀ ≤ 0 := le_of_tendsto_of_tendsto he hc hS
  have hge : 0 ≤ metricEnergy W₀ y₀ := by simpa only [metricEnergy, dot, star_trivial] using hPSD.2 y₀
  exact (posSemidef_energy_zero_iff hPSD y₀).mp (le_antisymm hle hge)

theorem visibility_limit {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {W : ι → Mat n} {W₀ : Mat n} {g : ι → Vec n} {g₀ : Vec n} (m : ℝ)
    (hWlim : Tendsto W l (𝓝 W₀)) (hglim : Tendsto g l (𝓝 g₀))
    (hV : ∀ᶠ a in l, m ≤ metricEnergy (W a) (g a)) : m ≤ metricEnergy W₀ g₀ := by
  exact ge_of_tendsto
    (continuous_metricEnergy.continuousAt.tendsto.comp (hWlim.prodMk_nhds hglim)) hV

open TransportedCertificate

/-- Actual source accessible-pair result. Pair eligibility and the threshold
are supplied on a tail. In particular, access is not inferred from arbitrary
limiting active gradients. -/
theorem accessible_jump_annihilated {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (B : VisibilitySecantCertificate F K fstar c₁ c₂ η)
    (x z g h : ι → Vec n) (W₀ : Mat n) (jump : Vec n)
    (hp : ∀ᶠ a in l, x a ∈ positiveBand F K fstar η ∧ z a ∈ positiveBand F K fstar η ∧
      EligiblePair F c₁ c₂ (x a) (z a) (g a) (h a))
    (hd : Tendsto (fun a => pairDecrease (x a) (z a) (g a)) l (𝓝 0))
    (ht : Tendsto (fun a => pairCurvature (x a) (z a) (g a) (h a)) l (𝓝 0))
    (hy : Tendsto (fun a => h a - g a) l (𝓝 jump))
    (hWlim : Tendsto (fun a => B.W (z a)) l (𝓝 W₀)) : W₀.mulVec jump = 0 := by
  have hsmall : ∀ᶠ a in l, pairDecrease (x a) (z a) (g a) ≤ B.δ :=
    (hd.eventually (eventually_lt_nhds B.delta_pos)).mono (fun a ha => ha.le)
  refine suppression_limit_annihilates hWlim hy ht ?_ B.C ?_
  · filter_upwards [hp] with a ha
    exact B.positive_semidefinite _ ha.2.1 ha.2.2.gradient_z.differentiableAt
  · filter_upwards [hp, hsmall] with a ha hs
    exact B.secant _ _ _ _ ha.1 ha.2.1 ha.2.2 hs

/-- A continuous finite extension supplies the field limit required in the
source interpretation; this is an explicit hypothesis, not a property of all
certificate fields. -/
theorem accessible_jump_annihilated_of_continuousAt {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l]
    {F : Vec n → ℝ} {K : Set (Vec n)} {fstar c₁ c₂ η : ℝ}
    (B : VisibilitySecantCertificate F K fstar c₁ c₂ η)
    (x z g h : ι → Vec n) (p jump : Vec n)
    (hp : ∀ᶠ a in l, x a ∈ positiveBand F K fstar η ∧ z a ∈ positiveBand F K fstar η ∧
      EligiblePair F c₁ c₂ (x a) (z a) (g a) (h a))
    (hd : Tendsto (fun a => pairDecrease (x a) (z a) (g a)) l (𝓝 0))
    (ht : Tendsto (fun a => pairCurvature (x a) (z a) (g a) (h a)) l (𝓝 0))
    (hy : Tendsto (fun a => h a - g a) l (𝓝 jump))
    (hz : Tendsto z l (𝓝 p)) (hc : ContinuousAt B.W p) : (B.W p).mulVec jump = 0 :=
  accessible_jump_annihilated B x z g h (B.W p) jump hp hd ht hy (hc.tendsto.comp hz)

/-- Two abstract active-gradient vectors, used only for the algebraic scope
countermodel below. They are not asserted to form an actual BFGS trajectory. -/
def countermodelGradients : Fin 2 → Vec 1 := ![fun _ => 1, fun _ => 2]

def countermodelAccessible : Empty → Vec 1 := fun e => nomatch e

/-- Algebraic countermodel to replacing the accessible jump span by the span
of all active differences without justification: active gradients 1 and 2,
no accessible jumps, and W=I have positive visibility but zero common tangent
component for the full active-difference span. This is not an objective-level
or BFGS counterexample. -/
theorem active_accessible_span_countermodel :
    (1 : Mat 1).PosDef ∧
    (∀ i, 0 < metricEnergy (1 : Mat 1) (countermodelGradients i)) ∧
    (∀ j, (1 : Mat 1).mulVec (countermodelAccessible j) = 0) ∧
    (tangentSpace (fun i => euclideanVector (countermodelGradients i))).orthogonalProjection
      (euclideanVector (countermodelGradients 0)) = 0 ∧
    (Submodule.span ℝ (Set.range (fun i => euclideanVector (countermodelAccessible i))))ᗮ.orthogonalProjection
      (euclideanVector (countermodelGradients 0)) ≠ 0 := by
  have hV : ∀ i, 0 < metricEnergy (1 : Mat 1) (countermodelGradients i) := by
    intro i
    fin_cases i <;> norm_num [countermodelGradients, metricEnergy, dot, Fin.sum_univ_one]
  have hA : ∀ j, (1 : Mat 1).mulVec (countermodelAccessible j) = 0 := fun j => nomatch j
  refine ⟨Matrix.PosDef.one, hV, hA, ?_, visible_accessible_projection_ne_zero 1 _ hA _ (hV 0)⟩
  rw [Submodule.orthogonalProjection_eq_zero_iff]
  change euclideanVector (countermodelGradients 0) ∈
    (jumpSpace (fun i => euclideanVector (countermodelGradients i)))ᗮᗮ
  rw [Submodule.orthogonal_orthogonal]
  have hd := vsub_mem_vectorSpan ℝ
    (Set.mem_range_self (f := fun i => euclideanVector (countermodelGradients i)) (1 : Fin 2))
    (Set.mem_range_self (f := fun i => euclideanVector (countermodelGradients i)) (0 : Fin 2))
  have he : euclideanVector (countermodelGradients 1) - euclideanVector (countermodelGradients 0) =
      euclideanVector (countermodelGradients 0) := by
    ext i
    norm_num [countermodelGradients, euclideanVector]
  simpa only [vsub_eq_sub, he] using hd

end BfgsVerification.AccessibleJumpGeometry
