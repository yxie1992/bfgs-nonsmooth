import BfgsVerification.MaxAffineBasin

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace MaxAffine.Family
variable {n m : ℕ} (P : MaxAffine.Family n m)

theorem branch_hasGradient (i : Fin m) (x : Vec n) :
    HasFDerivAt (P.branch i) (gradientFunctional (P.a i)) x := by
  simpa only [branch,gradientFunctional_apply] using (gradientFunctional (P.a i)).hasFDerivAt.add_const (P.b i)

theorem active_supports {i : Fin m} {x : Vec n} (hi : P.branch i x = P.objective x) :
    Homogeneous.Supports P.objective x (P.a i) := by
  intro z
  have hb := P.branch_le i z
  rw [← hi] at *
  simp only [branch] at hb ⊢
  simp only [dot,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib] at hb ⊢
  linarith

theorem active_eq_gradient {i : Fin m} {x g : Vec n} (hi : P.branch i x = P.objective x)
    (hg : HasFDerivAt P.objective (gradientFunctional g) x) : P.a i = g :=
  supporting_vector_eq_gradient (P.active_supports hi) hg

theorem strict_active_eventuallyEq {i : Fin m} {x : Vec n}
    (hi : ∀ j, j ≠ i → P.branch j x < P.branch i x) :
    P.objective =ᶠ[𝓝 x] P.branch i := by
  have he : ∀ᶠ z in 𝓝 x, ∀ j, P.branch j z ≤ P.branch i z := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j=i
    · subst j
      exact Eventually.of_forall (fun _ => le_rfl)
    have hh : ∀ᶠ z in 𝓝 x, P.branch j z < P.branch i z :=
      (isOpen_lt (P.branch_continuous j) (P.branch_continuous i)).mem_nhds (hi j hj)
    exact hh.mono (fun _ h => h.le)
  filter_upwards [he] with z hz
  apply le_antisymm _ (P.branch_le i z)
  apply Finset.sup'_le
  intro j _
  exact hz j

theorem strict_active_hasGradient {i : Fin m} {x : Vec n}
    (hi : ∀ j, j ≠ i → P.branch j x < P.branch i x) :
    HasFDerivAt P.objective (gradientFunctional (P.a i)) x :=
  (P.branch_hasGradient i x).congr_of_eventuallyEq (P.strict_active_eventuallyEq hi)

end MaxAffine.Family
end BfgsVerification
