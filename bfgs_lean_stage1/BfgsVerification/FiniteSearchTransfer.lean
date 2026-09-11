import BfgsVerification.DeterministicLineSearch

noncomputable section
namespace BfgsVerification.DeterministicLineSearch

/-- Agreement on the source's actual finite history suffices to preserve the
entire branching search. No comparison is required at an unqueried point. -/
theorem search_history_congr {n : ℕ} (Q F : Vec n → ℝ) (x p g u v h : Vec n)
    (c₁ c₂ : ℝ) (fuel : ℕ) (l : ℝ) (upper : Option ℝ) (a : ℝ)
    (hc : ∀b∈(search Q x p g c₁ c₂ fuel l upper a).2,
      (Armijo F u v h c₁ b↔Armijo Q x p g c₁ b) ∧
      (Wolfe F u v h c₂ b↔Wolfe Q x p g c₂ b)) :
    search F u v h c₁ c₂ fuel l upper a=search Q x p g c₁ c₂ fuel l upper a := by
  induction fuel generalizing l upper a with
  | zero => simp only [search]
  | succ fuel ih =>
    by_cases hA : Armijo Q x p g c₁ a
    · by_cases hW : Wolfe Q x p g c₂ a
      · have he : search Q x p g c₁ c₂ (fuel+1) l upper a=(some a,[a]) := search_accept fuel hA hW
        have ha := hc a (by rw [he]; simp)
        rw [search_accept fuel (ha.1.mpr hA) (ha.2.mpr hW),he]
      · have he : search Q x p g c₁ c₂ (fuel+1) l upper a=
          let r := search Q x p g c₁ c₂ fuel a upper (nextTrial a upper)
          (r.1,a::r.2) := by rw [search,if_pos hA,if_neg hW]
        have ha := hc a (by rw [he]; simp)
        have hh := ih a upper (nextTrial a upper) (fun b hb => hc b (by rw [he]; exact List.mem_cons_of_mem a hb))
        rw [search,if_pos (ha.1.mpr hA),if_neg (fun hw => hW (ha.2.mp hw)),hh]
        exact he.symm
    · have he : search Q x p g c₁ c₂ (fuel+1) l upper a=
          let r := search Q x p g c₁ c₂ fuel l (some a) ((l+a)/2)
          (r.1,a::r.2) := search_armijo_reject fuel hA
      have ha := hc a (by rw [he]; simp)
      have hh := ih l (some a) ((l+a)/2) (fun b hb => hc b (by rw [he]; exact List.mem_cons_of_mem a hb))
      rw [search_armijo_reject fuel (fun hw => hA (ha.1.mp hw)),hh]
      exact he.symm

end BfgsVerification.DeterministicLineSearch
