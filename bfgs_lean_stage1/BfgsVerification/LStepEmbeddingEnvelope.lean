import BfgsVerification.LStepEmbeddingPolyhedral

noncomputable section
open scoped Topology BigOperators
open Set Filter Matrix
namespace BfgsVerification.LStepEmbedding
open LEmbedding LScalarGeometric

def CountableIndex := Option (Fin 3 × Option ℕ)

theorem countable_index : Countable CountableIndex := by
  dsimp [CountableIndex]
  infer_instance

def countableLinear : CountableIndex → Vec 2 →L[ℝ] ℝ
  | none => ContinuousLinearMap.proj 1
  | some (i,none) => -gradientFunctional (slope i)
  | some (i,some n) => scale n • gradientFunctional (slope i)

def countableOffset : CountableIndex → ℝ
  | none => 0
  | some (_,none) => 0
  | some (i,some n) => (1-parameter i)*(scale n)^2

theorem countableFamily_old (i : Fin 3) (j : Option ℕ) (x : Vec 2) :
    countableLinear (some (i,j)) x+countableOffset (some (i,j))=
      LScalarStep.affineFamily (parameter i) j (dot (slope i) x) := by
  cases j <;> simp [countableLinear,countableOffset,LScalarStep.affineFamily,
    LScalarStep.line,ContinuousLinearMap.smul_apply,gradientFunctional_apply]

theorem residual_countable_max (x : Vec 2) :
    IsGreatest (range (fun j => countableLinear j x+countableOffset j)) (residual x) := by
  have hscalar (i : Fin 3) := LScalarStep.phi_countable_max
    (parameter_bounds i).1.le (parameter_bounds i).2.le (dot (slope i) x)
  constructor
  · obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      Finset.univ_nonempty (fun i => residualBranch i x)
    change residual x=residualBranch i x at hi
    have hold (j : Fin 3) (hj : i=j.castSucc) : residual x ∈
        range (fun j => countableLinear j x+countableOffset j) := by
      obtain ⟨k,hk⟩ := (hscalar j).1
      refine ⟨some (j,k),?_⟩
      change countableLinear (some (j,k)) x+countableOffset (some (j,k))=residual x
      rw [countableFamily_old]
      exact hk.trans (by rw [hi,hj,residualBranch_old])
    fin_cases i
    · exact hold 0 rfl
    · exact hold 1 rfl
    · exact hold 2 rfl
    · exact ⟨none,by simpa [countableLinear,countableOffset,residualBranch] using hi.symm⟩
  · rintro _ ⟨j,rfl⟩
    cases j with
    | none => simpa only [countableLinear,countableOffset,ContinuousLinearMap.proj_apply,add_zero]
        using residualBranch_le 3 x
    | some p =>
      obtain ⟨i,j⟩ := p
      change countableLinear (some (i,j)) x+countableOffset (some (i,j))≤residual x
      rw [countableFamily_old]
      have hb := residualBranch_le i.castSucc x
      rw [residualBranch_old] at hb
      exact ((hscalar i).2 (mem_range_self j)).trans hb

end BfgsVerification.LStepEmbedding
