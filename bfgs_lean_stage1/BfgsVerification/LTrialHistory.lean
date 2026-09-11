import BfgsVerification.LFlattenNeighborhood

noncomputable section
namespace BfgsVerification.SeedOrbit

theorem trial_history_witness (j : Fin 3) {a : ℝ} (ha : a∈trialHistory j) :
    ∃q : Fin 9,trialPhase q=j ∧ trialLength q=a := by
  fin_cases j
  · change a∈[1] at ha
    simp only [List.mem_singleton] at ha
    subst a
    exact ⟨0,rfl,rfl⟩
  · change a∈[1,1/2,1/4] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    · exact ⟨1,rfl,rfl⟩
    · exact ⟨2,rfl,rfl⟩
    · exact ⟨3,rfl,rfl⟩
  · change a∈[1,1/2,1/4,1/8,1/16] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    · exact ⟨4,rfl,rfl⟩
    · exact ⟨5,rfl,rfl⟩
    · exact ⟨6,rfl,rfl⟩
    · exact ⟨7,rfl,rfl⟩
    · exact ⟨8,rfl,rfl⟩

theorem query_in_history (q : Fin 9) : trialLength q∈trialHistory (trialPhase q) := by
  fin_cases q <;> norm_num [trialLength,trialPhase,trialHistory,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail]

  all_goals change _∈[(1 : ℝ),1/2,1/4,1/8,1/16]
  all_goals norm_num

end BfgsVerification.SeedOrbit
