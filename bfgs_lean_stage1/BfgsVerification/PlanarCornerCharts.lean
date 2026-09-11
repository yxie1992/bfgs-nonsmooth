import BfgsVerification.PlanarActiveGeometry
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Actual C² corner level curves from the inverse function theorem applied to
the two branch values. Invertibility is proved from the actual gradient rows. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarCornerCharts
open HomogeneousPlanar AffineProjection

def branchValues (f : Fin 2 → Vec 2 → ℝ) (x : Vec 2) : Vec 2 := fun i => f i x

def rowEquiv (a b : Vec 2) (hd : pairDet a b ≠ 0) : Vec 2 ≃L[ℝ] Vec 2 :=
  ContinuousLinearEquiv.equivOfInverse (matrixCLM (pairMatrix a b)) (matrixCLM (pairMatrix a b)⁻¹)
    (by
      intro x
      simp only [matrixCLM_apply,Matrix.mulVec_mulVec]
      rw [Matrix.nonsing_inv_mul _ (by simpa only [pairMatrix_det] using hd.isUnit),Matrix.one_mulVec])
    (by
      intro x
      simp only [matrixCLM_apply,Matrix.mulVec_mulVec]
      rw [Matrix.mul_nonsing_inv _ (by simpa only [pairMatrix_det] using hd.isUnit),Matrix.one_mulVec])

theorem rowEquiv_apply (a b x : Vec 2) (hd : pairDet a b ≠ 0) :
    rowEquiv a b hd x = (pairMatrix a b).mulVec x := rfl

theorem branchValues_hasFDerivAt {f : Fin 2 → Vec 2 → ℝ} {x a b : Vec 2}
    (h0 : HasFDerivAt (f 0) (gradientFunctional a) x)
    (h1 : HasFDerivAt (f 1) (gradientFunctional b) x) (hd : pairDet a b ≠ 0) :
    HasFDerivAt (branchValues f) (rowEquiv a b hd : Vec 2 →L[ℝ] Vec 2) x := by
  have hg : HasFDerivAt (branchValues f)
      (ContinuousLinearMap.pi (fun i : Fin 2 => if i=0 then gradientFunctional a else gradientFunctional b)) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa only [if_pos rfl] using h0
    · simpa using h1
  convert hg using 1
  ext z i
  fin_cases i <;> simp [rowEquiv_apply,branchValues,Matrix.mulVec,pairMatrix,dot]

/-- The actual inverse chart parameterizes all nearby common branch levels. -/
theorem exists_corner_chart {f : Fin 2 → Vec 2 → ℝ} {x a b : Vec 2} {ℓ : ℝ}
    (hC : ∀ i, ContDiffAt ℝ 2 (f i) x)
    (h0 : HasFDerivAt (f 0) (gradientFunctional a) x)
    (h1 : HasFDerivAt (f 1) (gradientFunctional b) x)
    (hd : pairDet a b ≠ 0) (hf0 : f 0 x=ℓ) (hf1 : f 1 x=ℓ) :
    ∃ p : ℝ → Vec 2, p ℓ=x ∧ ContDiffAt ℝ 2 p ℓ ∧
      (∀ᶠ t in 𝓝 ℓ, ∀ i, f i (p t)=t) ∧
      (∀ᶠ z in 𝓝 x, (∀ i, f i z=f 0 z) → z=p (f 0 z)) := by
  have hG : ContDiffAt ℝ 2 (branchValues f) x := contDiffAt_pi.mpr hC
  have hG' := branchValues_hasFDerivAt h0 h1 hd
  let e := rowEquiv a b hd
  let q := hG.localInverse hG' (by norm_num)
  have hEq : branchValues f x = fun _ => ℓ := by
    ext i
    fin_cases i
    · exact hf0
    · exact hf1
  let p : ℝ → Vec 2 := fun t => q (fun _ => t)
  have hp : p ℓ=x := by
    dsimp only [p,q]
    rw [← hEq]
    exact hG.localInverse_apply_image hG' (by norm_num)
  have hqC : ContDiffAt ℝ 2 q (fun _ => ℓ) := by
    rw [← hEq]
    exact hG.to_localInverse hG' (by norm_num)
  have hs := hG.hasStrictFDerivAt' hG' (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hright : ∀ᶠ y in 𝓝 (fun _ : Fin 2 => ℓ), branchValues f (q y)=y := by
    rw [← hEq]
    exact hs.eventually_right_inverse
  have hleft : ∀ᶠ z in 𝓝 x, q (branchValues f z)=z := hs.eventually_left_inverse
  refine ⟨p,hp,hqC.comp ℓ (by fun_prop),?_,?_⟩
  · have hc : Continuous (fun t : ℝ => (fun _ : Fin 2 => t)) := by fun_prop
    filter_upwards [(hc.tendsto ℓ).eventually hright] with t ht
    exact fun i => congrFun ht i
  · filter_upwards [hleft] with z hz hfi
    have he : branchValues f z=fun _ => f 0 z := funext hfi
    rw [he] at hz
    exact hz.symm

/-- The level curve is obtained from the actual branch values, and the
reference level has just one corner in a neighborhood. -/
theorem exists_corner_curve {f : Fin 2 → Vec 2 → ℝ} {x a b : Vec 2} {ℓ : ℝ}
    (hC : ∀ i, ContDiffAt ℝ 2 (f i) x)
    (h0 : HasFDerivAt (f 0) (gradientFunctional a) x)
    (h1 : HasFDerivAt (f 1) (gradientFunctional b) x)
    (hd : pairDet a b ≠ 0) (hf0 : f 0 x=ℓ) (hf1 : f 1 x=ℓ) :
    ∃ p : ℝ → Vec 2, p ℓ=x ∧ ContDiffAt ℝ 2 p ℓ ∧
      (∀ᶠ t in 𝓝 ℓ, ∀ i, f i (p t)=t) ∧
      (∀ᶠ z in 𝓝 x, (∀ i, f i z=ℓ) → z=x) := by
  obtain ⟨p,hp,hpC,hlevel,hinv⟩ := exists_corner_chart hC h0 h1 hd hf0 hf1
  refine ⟨p,hp,hpC,hlevel,?_⟩
  filter_upwards [hinv] with z hz hfi
  have he := hz (fun i => (hfi i).trans (hfi 0).symm)
  rw [hfi 0,hp] at he
  exact he

/-- C² point curves have C¹ actual level velocities, exactly the regularity
available from the source's C² branch hypothesis. -/
theorem curve_velocity_contDiffAt {p : ℝ → Vec 2} {t : ℝ} (hp : ContDiffAt ℝ 2 p t) :
    ContDiffAt ℝ 1 (deriv p) t := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ p) t := hp.fderiv_right (by norm_num)
  change ContDiffAt ℝ 1 (fun s => fderiv ℝ p s 1) t
  exact hd.clm_apply contDiffAt_const

/-- Differentiating the defining equations gives the exact common increase
rate for every actual branch derivative along a differentiable level curve. -/
theorem curve_velocity_pairing {f : Fin 2 → Vec 2 → ℝ} {p : ℝ → Vec 2}
    {g : Fin 2 → Vec 2} {v : Vec 2} {t : ℝ}
    (hp : HasDerivAt p v t) (hf : ∀ i, HasFDerivAt (f i) (gradientFunctional (g i)) (p t))
    (he : ∀ᶠ s in 𝓝 t, ∀ i, f i (p s)=s) : ∀ i, dot (g i) v=1 := by
  intro i
  have hcomp := (hf i).comp_hasDerivAt t hp
  have hid : HasDerivAt (fun s => f i (p s)) 1 t :=
    (hasDerivAt_id t).congr_of_eventuallyEq (he.mono (fun s hs => hs i))
  simpa using hcomp.unique hid

end PlanarCornerCharts
end BfgsVerification
