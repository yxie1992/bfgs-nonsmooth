import BfgsVerification.LBlockStableOrbit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.LBlockInvertibility
open LBlockSplitting

theorem block_injective {F : State →L[ℝ] State} {alpha rho a b c d : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F alpha rho a b c d p q h k) (ha : alpha≠0) (hr : rho≠0)
    (hdet : a*d-b*c≠0) : Function.Injective F := by
  apply (injective_iff_map_eq_zero F).mpr
  intro w hw
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  have h2 := congrFun hw 2
  have h3 := congrFun hw 3
  have h4 := congrFun hw 4
  rw [hF] at h0 h1 h2 h3 h4
  change rho*w 4=0 at h4
  have hw4 : w 4=0 := (mul_eq_zero.mp h4).resolve_left hr
  change a*w 2+b*w 3+k 0*w 4=0 at h2
  change c*w 2+d*w 3+k 1*w 4=0 at h3
  rw [hw4,mul_zero,add_zero] at h2 h3
  have hh2 : (a*d-b*c)*w 2=0 := by nlinarith [congrArg (fun x => x*d) h2,congrArg (fun x => x*b) h3]
  have hh3 : (a*d-b*c)*w 3=0 := by nlinarith [congrArg (fun x => x*c) h2,congrArg (fun x => x*a) h3]
  have hw2 : w 2=0 := (mul_eq_zero.mp hh2).resolve_left hdet
  have hw3 : w 3=0 := (mul_eq_zero.mp hh3).resolve_left hdet
  change alpha*w 0+p 0*w 2+q 0*w 3+h 0*w 4=0 at h0
  change alpha*w 1+p 1*w 2+q 1*w 3+h 1*w 4=0 at h1
  simp only [hw2,hw3,hw4,mul_zero,add_zero] at h0 h1
  have hw0 : w 0=0 := (mul_eq_zero.mp h0).resolve_left ha
  have hw1 : w 1=0 := (mul_eq_zero.mp h1).resolve_left ha
  ext i
  fin_cases i <;> assumption

theorem continuousLinearEquiv_of_block {F : State →L[ℝ] State} {alpha rho a b c d : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F alpha rho a b c d p q h k) (ha : alpha≠0) (hr : rho≠0)
    (hdet : a*d-b*c≠0) : ∃ E : State ≃L[ℝ] State, E.toContinuousLinearMap=F := by
  let E := (LinearEquiv.ofInjectiveEndo F.toLinearMap (block_injective hF ha hr hdet)).toContinuousLinearEquiv
  exact ⟨E,rfl⟩

/-- A smooth actual map with this invertible block derivative is a local smooth
diffeomorphism. The inverse identities hold on actual neighborhoods. -/
theorem local_smooth_inverse_of_block {T : State → State} {P : State} {F : State →L[ℝ] State}
    (hT : ContDiffAt ℝ ⊤ T P) (hD : HasFDerivAt T F P)
    {alpha rho a b c d : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F alpha rho a b c d p q h k) (ha : alpha≠0) (hr : rho≠0)
    (hdet : a*d-b*c≠0) :
    ∃ S : State → State, ContDiffAt ℝ ⊤ S (T P) ∧ S (T P)=P ∧
      (∀ᶠ x in 𝓝 P, S (T x)=x) ∧ (∀ᶠ y in 𝓝 (T P), T (S y)=y) := by
  obtain ⟨E,hE⟩ := continuousLinearEquiv_of_block hF ha hr hdet
  have hd : HasFDerivAt T E.toContinuousLinearMap P := by rwa [hE]
  have hn : (1 : WithTop ℕ∞) ≤ ⊤ := le_top
  let S := hT.localInverse hd hn
  have hs := hT.hasStrictFDerivAt' hd hn
  exact ⟨S,hT.to_localInverse hd hn,hT.localInverse_apply_image hd hn,
    hs.eventually_left_inverse,hs.eventually_right_inverse⟩

end BfgsVerification.LBlockInvertibility
