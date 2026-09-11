import BfgsVerification.PlanarNormalSectors

/-! Uniformity of the actual normalized corner sectors under continuous motion
of the two gradients and their common-level velocity. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarNormalGeometry

theorem normalSector_uniform_pairing (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) :
    ∃ η : ℝ, 0 < η ∧ ∀ w ∈ normalSector a b, η ≤ dot w v := by
  apply (normalSector_compact a b v ha hb).exists_forall_le'
  · exact (by unfold dot; fun_prop : Continuous (fun w : Vec 2 => dot w v)).continuousOn
  · exact fun w hw => normalSector_pairing_pos ha hb hw

theorem unitBlend_continuousAt_motion {a b : ℝ → Vec 2} {t r : ℝ} {v : Vec 2}
    (ha : ContinuousAt a t) (hb : ContinuousAt b t)
    (hva : dot (a t) v=1) (hvb : dot (b t) v=1) :
    ContinuousAt (fun z : ℝ × ℝ => unitBlend (a z.1) (b z.1) z.2) (t,r) := by
  have hc : ContinuousAt (fun z : ℝ × ℝ => blend (a z.1) (b z.1) z.2) (t,r) := by
    unfold blend
    exact (continuousAt_const.sub continuousAt_snd).smul (ha.comp continuousAt_fst) |>.add
      (continuousAt_snd.smul (hb.comp continuousAt_fst))
  have he : ContinuousAt
      (fun z : ℝ × ℝ => euclideanVector (blend (a z.1) (b z.1) z.2)) (t,r) :=
    (PiLp.continuous_equiv_symm _ _).continuousAt.comp hc
  exact (he.norm.inv₀ (blend_euclidean_norm_pos (a t) (b t) v hva hvb r).ne').smul hc

/-- A fixed open angular neighborhood of a corner sector continues to contain
its whole moving sector, uniformly over every convex-combination parameter. -/
theorem normalSector_eventually_subset {a b : ℝ → Vec 2} {t : ℝ} {v : Vec 2}
    (ha : ContinuousAt a t) (hb : ContinuousAt b t)
    (hva : dot (a t) v=1) (hvb : dot (b t) v=1)
    {U : Set (Vec 2)} (hU : IsOpen U) (hsub : normalSector (a t) (b t) ⊆ U) :
    ∀ᶠ s in 𝓝 t, normalSector (a s) (b s) ⊆ U := by
  have he : ∀ᶠ s in 𝓝 t, ∀ r ∈ Icc (0 : ℝ) 1, unitBlend (a s) (b s) r ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    exact (unitBlend_continuousAt_motion ha hb hva hvb).eventually
      (hU.mem_nhds (hsub (mem_image_of_mem _ hr)))
  filter_upwards [he] with s hs
  rintro w ⟨r,hr,rfl⟩
  exact hs r hr

/-- Positive pairing is uniform both in level and across the full moving normal
sector. Only continuity at the reference level is needed. -/
theorem normalSector_pairing_uniform_near {a b v : ℝ → Vec 2} {t : ℝ}
    (ha : ContinuousAt a t) (hb : ContinuousAt b t) (hv : ContinuousAt v t)
    (hva : dot (a t) (v t)=1) (hvb : dot (b t) (v t)=1) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ s in 𝓝 t, ∀ w ∈ normalSector (a s) (b s), η ≤ dot w (v s) := by
  obtain ⟨η,hη,hbound⟩ := normalSector_uniform_pairing (a t) (b t) (v t) hva hvb
  refine ⟨η/2,half_pos hη,?_⟩
  have he : ∀ᶠ s in 𝓝 t, ∀ r ∈ Icc (0 : ℝ) 1,
      η/2 < dot (unitBlend (a s) (b s) r) (v s) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hc : ContinuousAt
        (fun z : ℝ × ℝ => dot (unitBlend (a z.1) (b z.1) z.2) (v z.1)) (t,r) := by
      have h1 := unitBlend_continuousAt_motion (r := r) ha hb hva hvb
      have h2 : ContinuousAt (fun z : ℝ × ℝ => v z.1) (t,r) := hv.comp continuousAt_fst
      simp only [dot,Fin.sum_univ_two]
      exact (((continuous_apply 0).continuousAt.comp h1).mul ((continuous_apply 0).continuousAt.comp h2)).add (((continuous_apply 1).continuousAt.comp h1).mul ((continuous_apply 1).continuousAt.comp h2))
    exact hc.eventually (lt_mem_nhds ((half_lt_self hη).trans_le
      (hbound _ (mem_image_of_mem _ hr))))
  filter_upwards [he] with s hs
  rintro w ⟨r,hr,rfl⟩
  exact (hs r hr).le

end PlanarNormalGeometry
end BfgsVerification
