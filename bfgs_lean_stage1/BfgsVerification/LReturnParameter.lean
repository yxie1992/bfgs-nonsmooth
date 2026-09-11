import BfgsVerification.LNormalizedReturn

noncomputable section
open scoped Topology
open Matrix
namespace BfgsVerification.LReturnParameter
open SeedOrbit LNormalizedReturn

def parameterScale (μ : ℝ) : State →L[ℝ] State :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2,ContinuousLinearMap.proj 3,μ • ContinuousLinearMap.proj 4]

theorem parameterScale_apply (μ : ℝ) (w : State) :
    parameterScale μ w= ![w 0,w 1,w 2,w 3,μ*w 4] := by
  ext i
  fin_cases i <;> rfl

theorem parameterScale_seed (μ : ℝ) : parameterScale μ seed=seed := by
  ext i
  fin_cases i <;> simp [parameterScale,seed,LNormalizedReturn.seed,Matrix.cons_val]

theorem parameterScale_initial (μ : ℝ) (w : State) : initial (parameterScale μ w)=initial w := by
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem parameterScale_scale (μ : ℝ) (w : State) : scale (parameterScale μ w)=μ*scale w := rfl

theorem parameter_substep (μ τ : ℝ) (j : Fin 3) (s : PhaseState) :
    substep 1 (μ*τ) j s=substep μ τ j s := by
  simp only [substep,step,currentGradient,secant,one_mul]

theorem parameter_internal (μ : ℝ) (w : State) (k : ℕ) :
    internal 1 (parameterScale μ w) k=internal μ w k := by
  induction k with
  | zero => exact parameterScale_initial μ w
  | succ k ih => rw [internal,parameterScale_scale,ih,parameter_substep,← internal]

theorem parameter_returnFactor (μ : ℝ) (w : State) :
    returnFactor 1 (parameterScale μ w)=returnFactor μ w := by
  simp only [returnFactor,parameter_internal]

theorem parameter_semiconjugacy (μ : ℝ) (w : State) :
    returnMap 1 (parameterScale μ w)=parameterScale μ (returnMap μ w) := by
  conv_rhs => rw [parameterScale_apply]
  simp only [returnMap,parameter_internal,parameter_returnFactor,parameterScale_scale]
  ext i
  fin_cases i <;> simp [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  all_goals ring

theorem derivative_parameter_semiconjugacy (μ : ℝ) :
    (fderiv ℝ (returnMap 1) seed).comp (parameterScale μ)=
      (parameterScale μ).comp (fderiv ℝ (returnMap μ) seed) := by
  have h1 := (analytic_returnMap_seed (1 : ℝ)).differentiableAt.hasFDerivAt
  have hμ := (analytic_returnMap_seed μ).differentiableAt.hasFDerivAt
  have hp := (parameterScale μ).hasFDerivAt (x := seed)
  have hleft : HasFDerivAt (fun w => returnMap 1 (parameterScale μ w))
      ((fderiv ℝ (returnMap 1) seed).comp (parameterScale μ)) seed := by
    have h1' : HasFDerivAt (returnMap 1) (fderiv ℝ (returnMap 1) seed) (parameterScale μ seed) := by
      rw [parameterScale_seed]
      exact h1
    exact h1'.comp seed hp
  have hright := ((parameterScale μ).hasFDerivAt (x := returnMap μ seed)).comp seed hμ
  have he : (fun w => returnMap 1 (parameterScale μ w))=
      (fun w => parameterScale μ (returnMap μ w)) := funext (parameter_semiconjugacy μ)
  rw [he] at hleft
  exact hleft.unique hright

/-- The two upper tau blocks are mu times fixed coefficients, literally
independent of mu; the source's unused coefficient vectors need no enclosure. -/
theorem derivative_tau_column (μ : ℝ) (i : Fin 5) (hi : i.val<4) :
    (fderiv ℝ (returnMap μ) seed (Pi.single (4 : Fin 5) 1)) i=
      μ*(fderiv ℝ (returnMap 1) seed (Pi.single (4 : Fin 5) 1)) i := by
  have he := congrArg (fun L : State →L[ℝ] State => L (Pi.single (4 : Fin 5) 1))
    (derivative_parameter_semiconjugacy μ)
  have hp : parameterScale μ (Pi.single (4 : Fin 5) 1)=μ • (Pi.single (4 : Fin 5) 1 : State) := by
    ext j
    fin_cases j <;> simp [parameterScale,Pi.single_apply,Matrix.cons_val]
  dsimp only at he
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,hp,map_smul] at he
  have h := congrFun he i
  fin_cases i <;> norm_num at hi
  all_goals simpa [parameterScale,Matrix.cons_val,Matrix.cons_val_two] using h.symm

theorem parameterScale_coordinate (μ : ℝ) (v : State) (i : Fin 5) (hi : i.val<4) :
    parameterScale μ v i=v i := by
  fin_cases i <;> norm_num at hi
  all_goals rfl

theorem parameterScale_horizontal_unit (μ : ℝ) (j : Fin 5) (hj : j.val<4) :
    parameterScale μ (Pi.single j 1)= (Pi.single j 1 : State) := by
  ext i
  fin_cases j <;> norm_num at hj
  all_goals fin_cases i <;> simp [parameterScale,Pi.single_apply,Matrix.cons_val]

/-- The upper-left four-by-four block, including C, is independent of mu. -/
theorem derivative_horizontal_entries (μ : ℝ) (i j : Fin 5) (hi : i.val<4) (hj : j.val<4) :
    (fderiv ℝ (returnMap μ) seed (Pi.single j 1)) i=
      (fderiv ℝ (returnMap 1) seed (Pi.single j 1)) i := by
  have he := congrArg (fun L : State →L[ℝ] State => L (Pi.single j 1))
    (derivative_parameter_semiconjugacy μ)
  dsimp only at he
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,parameterScale_horizontal_unit μ j hj] at he
  have h := congrFun he i
  rw [parameterScale_coordinate μ _ i hi] at h
  exact h.symm

end BfgsVerification.LReturnParameter
