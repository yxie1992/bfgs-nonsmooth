import BfgsVerification.DEmbeddingObjective
import BfgsVerification.DScalarPlateauDerivative

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric

def center (n : ℕ) : Vec 2 := scale n • ![2,-32]

theorem center_argument (n : ℕ) (i : Fin 3) :
    dot (SeedOrbit.gradient seedC seedD i) (center n)=parameter i*scale n := by
  fin_cases i <;> simp [center, parameter, bStar, SeedOrbit.gradient, g0, g1, g2,
    dot, Fin.sum_univ_two] <;> ring

theorem translated_argument (n : ℕ) (i : Fin 3) (h : Vec 2) :
    dot (SeedOrbit.gradient seedC seedD i) (center n+h)=
      parameter i*scale n+dot (SeedOrbit.gradient seedC seedD i) h := by
  rw [show dot (SeedOrbit.gradient seedC seedD i) (center n+h)=
    dot (SeedOrbit.gradient seedC seedD i) (center n)+dot (SeedOrbit.gradient seedC seedD i) h from dotProduct_add _ _ _, center_argument]

theorem branch_plateau (n : ℕ) (i : Fin 3) {h : Vec 2}
    (hh : |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale n/2) :
    branch i.castSucc (center n+h)=(scale n)^3+(scale n)^2*dot (SeedOrbit.gradient seedC seedD i) h := by
  rw [branch_old, translated_argument]
  exact DScalar.phi_plateau (parameter_bounds i).1 (parameter_bounds i).2 n hh

theorem slab_vertical (n : ℕ) {h : Vec 2}
    (hh : ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale n/2) :
    |h 1| ≤ 8*scale n := by
  have h0 := abs_le.mp (hh 0)
  have h1 := abs_le.mp (hh 1)
  norm_num [SeedOrbit.gradient, g0, g1, dot, Fin.sum_univ_two] at h0 h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem last_branch_negative (n : ℕ) {h : Vec 2}
    (hh : ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale n/2) :
    branch 3 (center n+h)<0 := by
  have hu := (abs_le.mp (slab_vertical n hh)).2
  have ha := scale_pos n
  change scale n*(-32)+h 1<0
  linarith

theorem branch_plateau_positive (n : ℕ) (i : Fin 3) {h : Vec 2}
    (hh : |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale n/2) :
    0 < branch i.castSucc (center n+h) := by
  rw [branch_plateau n i hh]
  have ha := scale_pos n
  have ht := mul_le_mul_of_nonneg_left (abs_le.mp hh).1 (sq_nonneg (scale n))
  nlinarith [pow_pos ha 3]

theorem objective_eq_of_dom (i : Fin 4) (x : Vec 2) (hi : ∀ j, branch j x ≤ branch i x) :
    objective x=branch i x := le_antisymm (objective_le hi) (branch_le i x)

theorem local_cone (n : ℕ) {h : Vec 2}
    (hh : ∀ i : Fin 3, |dot (SeedOrbit.gradient seedC seedD i) h| ≤ scale n/2) :
    objective (center n+h)=(scale n)^3+(scale n)^2*SeedOrbit.objective seedC seedD h := by
  have hle (i : Fin 3) : dot (SeedOrbit.gradient seedC seedD i) h ≤ SeedOrbit.objective seedC seedD h := by
    simpa [MaxAffine.Family.branch, family] using (family seedC seedD).branch_le i h
  apply le_antisymm
  · apply objective_le
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (last_branch_negative n hh).le.trans ((branch_plateau_positive n 0 (hh 0)).le.trans (by
        rw [branch_plateau n 0 (hh 0)]
        exact add_le_add_left (mul_le_mul_of_nonneg_left (hle 0) (sq_nonneg _)) _))
    · rw [branch_plateau n j (hh j)]
      exact add_le_add_left (mul_le_mul_of_nonneg_left (hle j) (sq_nonneg _)) _
  · have hmax : SeedOrbit.objective seedC seedD h ≤
        (objective (center n+h)-(scale n)^3)/(scale n)^2 := by
      unfold SeedOrbit.objective MaxAffine.Family.objective
      apply Finset.sup'_le
      intro i _
      change dot (SeedOrbit.gradient seedC seedD i) h+0 ≤ _
      rw [add_zero, le_div_iff₀ (sq_pos_of_pos (scale_pos n))]
      have hi := branch_le i.castSucc (center n+h)
      rw [branch_plateau n i (hh i)] at hi
      nlinarith
    have hh' := (le_div_iff₀ (sq_pos_of_pos (scale_pos n))).mp hmax
    nlinarith

theorem objective_hasGradient_of_strict {x : Vec 2} {i : Fin 4} {g : Vec 2}
    (hi : ∀ j, j ≠ i → branch j x<branch i x)
    (hg : HasFDerivAt (branch i) (gradientFunctional g) x) :
    HasFDerivAt objective (gradientFunctional g) x := by
  have he : ∀ j : Fin 4, ∀ᶠ y in 𝓝 x, branch j y ≤ branch i y := by
    intro j
    by_cases hj : j=i
    · subst j; exact Filter.Eventually.of_forall (fun y => le_rfl)
    · have hlt : ∀ᶠ y in 𝓝 x, branch j y<branch i y :=
        (isOpen_lt (branch_contDiff j).continuous (branch_contDiff i).continuous).mem_nhds (hi j hj)
      exact hlt.mono (fun y hy => hy.le)
  have hall := Filter.eventually_all.mpr he
  have heq : objective =ᶠ[𝓝 x] branch i := hall.mono (fun y hy => objective_eq_of_dom i y hy)
  exact hg.congr_of_eventuallyEq heq

theorem strict_active_plateau {n : ℕ} {h : Vec 2} {i : Fin 3}
    (hh : ∀ j : Fin 3, |dot (SeedOrbit.gradient seedC seedD j) h| ≤ scale n/2)
    (hi : StrictActive seedC seedD h i) :
    ∀ j : Fin 4, j ≠ i.castSucc → branch j (center n+h)<branch i.castSucc (center n+h) := by
  intro j hj
  refine Fin.lastCases ?_ (fun q hq => ?_) j hj
  · intro _
    exact (last_branch_negative n hh).trans (branch_plateau_positive n i (hh i))
  · rw [branch_plateau n q (hh q), branch_plateau n i (hh i)]
    exact add_lt_add_left (mul_lt_mul_of_pos_left (hi q (fun he => hq (congrArg Fin.castSucc he)))
      (sq_pos_of_pos (scale_pos n))) _

theorem branch_hasGradient_plateau (n : ℕ) (i : Fin 3) {h : Vec 2}
    (hh : |dot (SeedOrbit.gradient seedC seedD i) h| < scale n/2) :
    HasFDerivAt (branch i.castSucc)
      (gradientFunctional ((scale n)^2 • SeedOrbit.gradient seedC seedD i)) (center n+h) := by
  have hd := branch_old_hasGradient i (center n+h)
  have hv := DScalar.phiFirst_plateau (parameter_bounds i).1 (parameter_bounds i).2 n hh
  simp only [ridgeGradient, translated_argument, hv] at hd
  exact hd

theorem objective_hasGradient_plateau {n : ℕ} {h : Vec 2} {i : Fin 3}
    (hh : ∀ j : Fin 3, |dot (SeedOrbit.gradient seedC seedD j) h| < scale n/2)
    (hi : StrictActive seedC seedD h i) :
    HasFDerivAt objective (gradientFunctional ((scale n)^2 • SeedOrbit.gradient seedC seedD i))
      (center n+h) :=
  objective_hasGradient_of_strict (strict_active_plateau (fun j => (hh j).le) hi)
    (branch_hasGradient_plateau n i (hh i))

end BfgsVerification.DEmbedding
