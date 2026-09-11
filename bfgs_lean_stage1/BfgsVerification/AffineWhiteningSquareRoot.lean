import BfgsVerification.AffineWhiteningSearch

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineWhitening
open AffineProjection
variable {n : ℕ}

def squareRoot (H : Mat n) (hH : H.PosDef) : Mat n := hH.posSemidef.sqrt

theorem squareRoot_square (H : Mat n) (hH : H.PosDef) : squareRoot H hH*squareRoot H hH=H :=
  hH.posSemidef.sqrt_mul_self

theorem squareRoot_transpose (H : Mat n) (hH : H.PosDef) : (squareRoot H hH)ᵀ=squareRoot H hH := by
  ext i j
  exact hH.posSemidef.posSemidef_sqrt.1.apply i j

theorem squareRoot_det_ne_zero (H : Mat n) (hH : H.PosDef) : (squareRoot H hH).det≠0 := by
  intro hz
  have hd := congrArg Matrix.det (squareRoot_square H hH)
  rw [Matrix.det_mul,hz,mul_zero] at hd
  exact hH.det_pos.ne' hd.symm

theorem squareRoot_initial_metric (H : Mat n) (hH : H.PosDef) : metric (squareRoot H hH) H=1 := by
  let A := squareRoot H hH
  have hd : A.det≠0 := squareRoot_det_ne_zero H hH
  have ht : (A⁻¹)ᵀ=A⁻¹ := by rw [Matrix.transpose_nonsing_inv,squareRoot_transpose]
  change A⁻¹*H*(A⁻¹)ᵀ=1
  rw [ht,← squareRoot_square H hH]
  change A⁻¹*(A*A)*A⁻¹=1
  rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hd.isUnit,Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hd.isUnit]

def whiten {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) :
    AdmissibleBFGSRun n (objective (squareRoot (R.H 0) R.initial_posDef) F) :=
  run _ (squareRoot_det_ne_zero _ R.initial_posDef) R

theorem whiten_initial {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F) : (whiten R).H 0=1 :=
  squareRoot_initial_metric _ R.initial_posDef

theorem fixed_initial_whitening {F : Vec n → ℝ} (H₀ : Mat n) (hH : H₀.PosDef)
    (R : AdmissibleBFGSRun n F) (hR : R.H 0=H₀) :
    (run (squareRoot H₀ hH) (squareRoot_det_ne_zero H₀ hH) R).H 0=1 := by
  rw [run_H,hR,squareRoot_initial_metric]

/-- A single actual SPD square root works for a whole family of starts with
one common initial metric; the coordinate change never depends on the start. -/
theorem fixed_family_identity {ι : Type*} {F : Vec n → ℝ}
    (H₀ : Mat n) (hH : H₀.PosDef) (R : ι → AdmissibleBFGSRun n F)
    (hR : ∀ i,(R i).H 0=H₀) :
    ∃ A : Mat n,A*A=H₀ ∧ Aᵀ=A ∧ ∃ hA : A.det≠0,
      (∀ i,(run A hA (R i)).H 0=1) ∧
      ∀i k fuel, DeterministicLineSearch.fromMetric (objective A F)
        ((run A hA (R i)).x k) ((run A hA (R i)).H k) (R i).c₁ (R i).c₂ fuel=
        DeterministicLineSearch.fromMetric F ((R i).x k) ((R i).H k) (R i).c₁ (R i).c₂ fuel := by
  refine ⟨squareRoot H₀ hH,squareRoot_square _ _,squareRoot_transpose _ _,
    squareRoot_det_ne_zero _ _,fun i => fixed_initial_whitening H₀ hH (R i) (hR i),?_⟩
  intro i k fuel
  exact fromMetric_equiv (squareRoot H₀ hH) (squareRoot_det_ne_zero H₀ hH) F
    ((R i).x k) ((R i).H k) (R i).c₁ (R i).c₂ fuel

end BfgsVerification.AffineWhitening
