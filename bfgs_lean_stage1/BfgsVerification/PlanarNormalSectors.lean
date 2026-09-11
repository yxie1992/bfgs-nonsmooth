import BfgsVerification.PlanarNormalGeometry

/-! Actual compact normal sectors of a planar regular corner. Normalization is
Euclidean; positivity is derived from the common level velocity. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarNormalGeometry

def blend (a b : Vec 2) (r : ℝ) : Vec 2 := (1-r) • a+r • b

def unitBlend (a b : Vec 2) (r : ℝ) : Vec 2 :=
  (‖euclideanVector (blend a b r)‖)⁻¹ • blend a b r

def normalSector (a b : Vec 2) : Set (Vec 2) := unitBlend a b '' Icc (0 : ℝ) 1

theorem blend_pairing (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) (r : ℝ) :
    dot (blend a b r) v=1 := by
  change dotProduct ((1-r) • a+r • b) v=1
  rw [add_dotProduct,smul_dotProduct,smul_dotProduct]
  change (1-r)*dot a v+r*dot b v=1
  rw [ha,hb]
  ring

theorem blend_ne_zero (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) (r : ℝ) :
    blend a b r ≠ 0 := by
  intro he
  have hp := blend_pairing a b v ha hb r
  rw [he] at hp
  norm_num [dot] at hp

theorem blend_euclidean_norm_pos (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) (r : ℝ) :
    0 < ‖euclideanVector (blend a b r)‖ := by
  apply norm_pos_iff.mpr
  intro he
  apply blend_ne_zero a b v ha hb r
  exact congrArg (fun x : EuclideanSpace ℝ (Fin 2) => fun i => x i) he

theorem unitBlend_norm_sq (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) (r : ℝ) :
    sqNorm (unitBlend a b r)=1 := by
  rw [unitBlend,CertificateGeometry.sqNorm_smul]
  have he : sqNorm (blend a b r) = ‖euclideanVector (blend a b r)‖ ^ 2 :=
    (FrameNorms.euclidean_norm_sq (euclideanVector (blend a b r))).symm
  rw [he]
  have hn := (blend_euclidean_norm_pos a b v ha hb r).ne'
  field_simp

theorem unitBlend_pairing_pos (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) (r : ℝ) :
    0 < dot (unitBlend a b r) v := by
  change 0 < dotProduct ((‖euclideanVector (blend a b r)‖)⁻¹ • blend a b r) v
  rw [smul_dotProduct]
  change 0 < (‖euclideanVector (blend a b r)‖)⁻¹*dot (blend a b r) v
  rw [blend_pairing a b v ha hb,mul_one]
  exact inv_pos.mpr (blend_euclidean_norm_pos a b v ha hb r)

theorem unitBlend_continuous (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) :
    Continuous (unitBlend a b) := by
  have hc : Continuous (blend a b) := by unfold blend; fun_prop
  have he : Continuous (fun r => euclideanVector (blend a b r)) :=
    (PiLp.continuous_equiv_symm _ _).comp hc
  exact (he.norm.inv₀ (fun r => (blend_euclidean_norm_pos a b v ha hb r).ne')).smul hc

theorem normalSector_compact (a b v : Vec 2) (ha : dot a v=1) (hb : dot b v=1) :
    IsCompact (normalSector a b) :=
  isCompact_Icc.image (unitBlend_continuous a b v ha hb)

theorem normalSector_norm_sq {a b v w : Vec 2} (ha : dot a v=1) (hb : dot b v=1)
    (hw : w ∈ normalSector a b) : sqNorm w=1 := by
  obtain ⟨r,_,rfl⟩ := hw
  exact unitBlend_norm_sq a b v ha hb r

theorem normalSector_pairing_pos {a b v w : Vec 2} (ha : dot a v=1) (hb : dot b v=1)
    (hw : w ∈ normalSector a b) : 0 < dot w v := by
  obtain ⟨r,_,rfl⟩ := hw
  exact unitBlend_pairing_pos a b v ha hb r

/-- Every unit normal in the actual corner sector supports the actual sublevel. -/
theorem normalSector_support {F : Vec 2 → ℝ} {p a b v w : Vec 2}
    (ha : Homogeneous.Supports F p a) (hb : Homogeneous.Supports F p b)
    (hva : dot a v=1) (hvb : dot b v=1) (hw : w ∈ normalSector a b) :
    SupportsSetAt {z | F z≤F p} p w := by
  obtain ⟨r,hr,rfl⟩ := hw
  let c := (‖euclideanVector (blend a b r)‖)⁻¹
  have hc : 0 < c := inv_pos.mpr (blend_euclidean_norm_pos a b v hva hvb r)
  have he : unitBlend a b r=(c*(1-r)) • a+(c*r) • b := by
    dsimp only [unitBlend,blend,c]
    module
  rw [he]
  apply supportsSetAt_of_two_supports ha hb hva hvb
  · exact mul_nonneg hc.le (sub_nonneg.mpr hr.2)
  · exact mul_nonneg hc.le hr.1
  · nlinarith

/-- Normal sectors at distinct points of one strict contour are disjoint. -/
theorem normalSectors_disjoint {F : Vec 2 → ℝ} (hF : ConvexOn ℝ univ F)
    {p z a b c d v u : Vec 2} (hpz : p ≠ z) (hlevel : F p=F z)
    (hstrict : ∀ x y : Vec 2, segment ℝ x y ⊆ frontier {w | F w≤F p} → x=y)
    (ha : Homogeneous.Supports F p a) (hb : Homogeneous.Supports F p b)
    (hc : Homogeneous.Supports F z c) (hd : Homogeneous.Supports F z d)
    (hva : dot a v=1) (hvb : dot b v=1) (huc : dot c u=1) (hud : dot d u=1) :
    Disjoint (normalSector a b) (normalSector c d) := by
  apply Set.disjoint_left.mpr
  intro w hwp hwz
  apply hpz
  apply points_equal_of_common_normal (isClosed_le (convex_continuous hF) continuous_const)
    (by simpa only [mem_univ, true_and] using hF.convex_le (F p)) hstrict
    (normalSector_support ha hb hva hvb hwp)
  simpa only [hlevel] using normalSector_support hc hd huc hud hwz

end PlanarNormalGeometry
end BfgsVerification
