import BfgsVerification.FiniteStepSums

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem finite_jump_corrected_locallyConstant (B : Finset ℝ) (f L : ℝ → ℤ)
    (hleft : ∀ a, ∀ᶠ x in 𝓝[<] a, f x = L a)
    (hright : ∀ a, ∀ᶠ x in 𝓝[≥] a, f x = f a)
    (hout : ∀ a, a ∉ B → L a = f a) :
    IsLocallyConstant (fun x => f x - finiteStepSum B (fun a => f a-L a) x) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  let j : ℝ → ℤ := fun b => f b-L b
  have hj : a ∉ B → j a = 0 := by intro ha; simp [j, hout a ha]
  have hs := finiteStepSum_eventuallyEq_of_not_mem (B.erase a) j
    (Finset.not_mem_erase a B)
  have he (x : ℝ) := finiteStepSum_erase B j a x hj
  change ∀ᶠ x in 𝓝 a, f x-finiteStepSum B j x = f a-finiteStepSum B j a
  rw [nhds_eq_nhdsWithin_sup_nhdsWithin a Iio_union_Ici.symm, eventually_sup]
  constructor
  · filter_upwards [hleft a, hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with x hfx hsx hx
    rw [he x, he a, if_neg (not_le_of_gt hx), if_pos le_rfl, hfx, hsx]
    dsimp [j]
    omega
  · filter_upwards [hright a, hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with x hfx hsx hx
    change a ≤ x at hx
    rw [he x, he a, if_pos hx, if_pos le_rfl, hfx, hsx]

theorem finite_jump_telescope (B : Finset ℝ) (f L : ℝ → ℤ)
    (hleft : ∀ a, ∀ᶠ x in 𝓝[<] a, f x = L a)
    (hright : ∀ a, ∀ᶠ x in 𝓝[≥] a, f x = f a)
    (hout : ∀ a, a ∉ B → L a = f a) (leftTail rightTail : ℤ)
    (hl : ∀ᶠ x in atBot, f x = leftTail)
    (hr : ∀ᶠ x in atTop, f x = rightTail) :
    ∑ a ∈ B, (f a-L a) = rightTail-leftTail := by
  have hc := finite_jump_corrected_locallyConstant B f L hleft hright hout
  obtain ⟨x,hfx,hsx⟩ := (hl.and (finiteStepSum_eventually_atBot B (fun a => f a-L a))).exists
  obtain ⟨y,hfy,hsy⟩ := (hr.and (finiteStepSum_eventually_atTop B (fun a => f a-L a))).exists
  have he := hc.apply_eq_of_preconnectedSpace x y
  change f x-finiteStepSum B (fun a => f a-L a) x =
    f y-finiteStepSum B (fun a => f a-L a) y at he
  rw [hfx, hsx, hfy, hsy] at he
  omega

end RealAlgebraicGeometry
end BfgsVerification
