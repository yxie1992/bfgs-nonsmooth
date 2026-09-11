import BfgsVerification.LPositiveOrbit
import BfgsVerification.LBlockColumns

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.LBlockSplitting

/-- Closed algebra-to-dynamics implication. The map and its actual strict
Jacobian remain explicit; no forward orbit or manifold is assumed. -/
theorem positive_orbit_of_block {T : State → State} {P : State} {F : State →L[ℝ] State}
    (hfix : T P=P) (hderiv : HasStrictFDerivAt T F P) (hP : P 4=0)
    {rho a b c d ls lu : ℝ} {p q h k : Vec 2}
    (hF : BlockForm F rho⁻¹ rho a b c d p q h k)
    (hr0 : 0<rho) (hr1 : rho<1) (hs0 : 0<ls) (hsr : ls<rho)
    (hu1 : 1<lu) (hua : lu<rho⁻¹) (hb : b≠0)
    (hsroot : (ls-a)*(ls-d)=b*c) (huroot : (lu-a)*(lu-d)=b*c)
    (V : Set State) (hV : V∈𝓝 P) :
    ∃ w : ℕ → State, (∀ n, w n∈V) ∧ Tendsto w atTop (𝓝 P) ∧ 0<w 0 4 ∧
      ∀ n, w (n+1)=T (w n) := by
  obtain ⟨E,hscale,A,L,hA,hL,hconj⟩ :=
    block_splitting hF hr0 hr1 hs0 hsr hu1 hua hb hsroot huroot
  exact positive_orbit_of_splitting hfix hderiv hP E hscale A L hA hL hconj V hV

theorem positive_scale_along_orbit {T : State → State} {V : Set State} {w : ℕ → State}
    (hw : ∀ n, w n∈V) (h0 : 0<w 0 4) (hrec : ∀ n, w (n+1)=T (w n))
    (hpres : ∀ x∈V, 0<x 4 → 0<T x 4) : ∀ n, 0<w n 4 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n hn => rw [hrec]; exact hpres _ (hw n) hn

end BfgsVerification.LBlockSplitting
