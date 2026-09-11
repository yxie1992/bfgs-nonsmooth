import BfgsVerification.AffineKinkCells

/-! Named literal scalar-residual source families, from actual affine data. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineKinks

def quantileLoss (τ r : ℝ) : ℝ := τ*max r 0+(1-τ)*max (-r) 0

theorem local_absolute_basin {n : ℕ} {ι : Type*} [Fintype ι] {F ψ : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (a : ι → Vec n) (b : ι → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ x ∈ U, F x=ψ x+∑ i, |dot (a i) x-b i|)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x=F star → x=star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  apply local_kink_basin hF (fun i => Kink.absolute (a i) (b i)) hU hψ hs _ hmin hu
  intro x hx
  simpa only [penalty,Kink.absolute_value] using hrep x hx

theorem local_hinge_basin {n : ℕ} {ι : Type*} [Fintype ι] {F ψ : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (a : ι → Vec n) (b : ι → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ x ∈ U, F x=ψ x+∑ i, max 0 (dot (a i) x-b i))
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x=F star → x=star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  apply local_kink_basin hF (fun i => Kink.hinge (a i) (b i)) hU hψ hs _ hmin hu
  intro x hx
  simpa only [penalty,Kink.hinge_value] using hrep x hx

theorem local_quantile_basin {n : ℕ} {ι : Type*} [Fintype ι] {F ψ : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (a : ι → Vec n) (b τ : ι → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ x ∈ U, F x=ψ x+∑ i, quantileLoss (τ i) (dot (a i) x-b i))
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x=F star → x=star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  apply local_kink_basin hF (fun i => Kink.quantile (a i) (b i) (τ i)) hU hψ hs _ hmin hu
  intro x hx
  simpa only [penalty,Kink.quantile_value,quantileLoss] using hrep x hx

/-- Generalized/fused ℓ1 data use an actual arbitrary rectangular matrix. -/
theorem local_matrix_l1_basin {n m : ℕ} {F ψ : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (A : Matrix (Fin m) (Fin n) ℝ) (b : Vec m)
    {U : Set (Vec n)} (hU : IsOpen U) (hψ : CenteredSmoothSublinear.LocallyC11On U ψ)
    {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ x ∈ U, F x=ψ x+∑ i, |(A.mulVec x-b) i|)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x=F star → x=star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  apply local_absolute_basin hF (fun i => A i) b hU hψ hs _ hmin hu
  exact hrep

/-- An exact representation transfers the derived all-full-space bad-ray
property to the named objective, including its actual derivatives. -/
theorem fullBFGS_step_of_representation {n : ℕ} {ι : Type*} [Fintype ι] {F ψ : Vec n → ℝ}
    (hψ : Differentiable ℝ ψ) (P : ι → Kink n)
    (hrep : ∀ z, F z=ψ z+penalty P z) (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hgn : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+bfgsStep H g t)) :
    ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt F (gradientFunctional h) (x+bfgsStep H g α) ∧
      F (x+bfgsStep H g α) < F x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  have he : F=objective ψ P := funext hrep
  subst F
  exact fullBFGS_step_exists hψ P hF x g H hH hgn hg hc₁ hc hc₂ L hL

theorem absolute_fullBFGS_step_exists {n : ℕ} {ι : Type*} [Fintype ι] {F ψ : Vec n → ℝ}
    (hψ : Differentiable ℝ ψ) (a : ι → Vec n) (b : ι → ℝ)
    (hrep : ∀ z, F z=ψ z+∑ i, |dot (a i) z-b i|) (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hgn : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+bfgsStep H g t)) :
    ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt F (gradientFunctional h) (x+bfgsStep H g α) ∧
      F (x+bfgsStep H g α) < F x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  apply fullBFGS_step_of_representation hψ (fun i => Kink.absolute (a i) (b i)) _ hF
    x g H hH hgn hg hc₁ hc hc₂ L hL
  simpa only [penalty,Kink.absolute_value] using hrep

theorem hinge_fullBFGS_step_exists {n : ℕ} {ι : Type*} [Fintype ι] {F ψ : Vec n → ℝ}
    (hψ : Differentiable ℝ ψ) (a : ι → Vec n) (b : ι → ℝ)
    (hrep : ∀ z, F z=ψ z+∑ i, max 0 (dot (a i) z-b i)) (hF : ConvexOn ℝ univ F)
    (x g : Vec n) (H : Mat n) (hH : H.PosDef) (hgn : g ≠ 0)
    (hg : HasFDerivAt F (gradientFunctional g) x)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ < c₂) (hc₂ : c₂ < 1)
    (L : ℝ) (hL : ∀ t : ℝ, 0 ≤ t → L ≤ F (x+bfgsStep H g t)) :
    ∃ α : ℝ, ∃ h : Vec n, 0 < α ∧
      HasFDerivAt F (gradientFunctional h) (x+bfgsStep H g α) ∧
      F (x+bfgsStep H g α) < F x+c₁*dot g (bfgsStep H g α) ∧
      c₂*dot g (bfgsStep H g α) < dot h (bfgsStep H g α) := by
  apply fullBFGS_step_of_representation hψ (fun i => Kink.hinge (a i) (b i)) _ hF
    x g H hH hgn hg hc₁ hc hc₂ L hL
  simpa only [penalty,Kink.hinge_value] using hrep

end BfgsVerification.AffineKinks
