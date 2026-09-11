import BfgsVerification.PlanarFieldVisibility

/-! Algebraic and limiting obstruction behind C's endpoint transversality.
The comparison field has a common positive rate on actual limiting supports. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarTransversality
open HomogeneousPlanar

/-- Determinant-zero planar directions satisfy the exact common-rate vector
identity, including arbitrary zero coordinates. -/
theorem parallel_pairing_identity (g e w : Vec 2) (hd : pairDet e w=0) :
    dot g w • e=dot g e • w := by
  simp only [pairDet] at hd
  ext i
  fin_cases i <;> simp only [dot,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
  · change (g 0*w 0+g 1*w 1)*e 0=(g 0*e 0+g 1*e 1)*w 0
    linear_combination g 1*hd
  · change (g 0*w 0+g 1*w 1)*e 1=(g 0*e 0+g 1*e 1)*w 1
    linear_combination -(g 0)*hd

/-- Equal positive comparison against both limiting supports rules out a
parallel nonzero descent direction satisfying weak Wolfe. No strict limiting
descent inequality is assumed. -/
theorem no_parallel_weak_wolfe (g h e w : Vec 2) {σ : ℝ} (hσ : 0<σ)
    (he : e ≠ 0) (hpos : 0<dot g w) (hcommon : dot g w=dot h w)
    (hdesc : dot g e ≤ 0) (hweak : σ*(-dot g e) ≤ dot (h-g) e)
    (hdet : pairDet e w=0) : False := by
  have hv := parallel_pairing_identity g e w hdet
  have hp := congrArg (fun v : Vec 2 => dot h v) hv
  simp only [dot_smul_right] at hp
  have hpair : dot h e=dot g e := by
    rw [← hcommon] at hp
    exact (mul_left_cancel₀ (ne_of_gt hpos) (by simpa only [mul_comm] using hp))
  have hzero : dot (h-g) e=0 := by
    change (h-g) ⬝ᵥ e=0
    rw [sub_dotProduct]
    exact sub_eq_zero.mpr hpair
  rw [hzero] at hweak
  have hge : dot g e=0 := by nlinarith
  rw [hge,zero_smul] at hv
  have hem : e=0 := (smul_eq_zero.mp hv).resolve_left (ne_of_gt hpos)
  exact he hem

/-- A convergent family of accepted-direction data cannot collapse to parallel
transport when the limiting field has the source's common positive pairing. -/
theorem limiting_determinant_ne_zero {ι : Type*} {l : Filter ι} [NeBot l]
    (g h e w : ι → Vec 2) {g0 h0 e0 w0 : Vec 2}
    (hg : Tendsto g l (𝓝 g0)) (hh : Tendsto h l (𝓝 h0))
    (he : Tendsto e l (𝓝 e0)) (hw : Tendsto w l (𝓝 w0))
    {σ : ℝ} (hσ : 0<σ) (he0 : e0 ≠ 0) (hpos : 0<dot g0 w0)
    (hcommon : dot g0 w0=dot h0 w0)
    (hdesc : ∀ᶠ i in l, dot (g i) (e i) ≤ 0)
    (hweak : ∀ᶠ i in l, σ*(-dot (g i) (e i)) ≤ dot (h i-g i) (e i)) :
    pairDet e0 w0 ≠ 0 := by
  have hd : Tendsto (fun i => dot (g i) (e i)) l (𝓝 (dot g0 e0)) :=
    continuous_dot.tendsto _ |>.comp (hg.prodMk_nhds he)
  have hdiff : Tendsto (fun i => dot (h i-g i) (e i)) l (𝓝 (dot (h0-g0) e0)) :=
    continuous_dot.tendsto _ |>.comp ((hh.sub hg).prodMk_nhds he)
  exact fun hdet => no_parallel_weak_wolfe g0 h0 e0 w0 hσ he0 hpos hcommon
    (le_of_tendsto hd hdesc) (le_of_tendsto_of_tendsto (hd.neg.const_mul σ) hdiff hweak) hdet

end PlanarTransversality
end BfgsVerification
