import BfgsVerification.RadialCentralDifference

/-! The no-radial-jump necessity in R's finite smooth-branch test. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.FiniteMaxRadial

theorem supporting_on {n : ℕ} {f : Vec n → ℝ} {U : Set (Vec n)}
    (hf : ConvexOn ℝ U f) {x z : Vec n} (hx : x ∈ U) (hz : z ∈ U)
    {g : Vec n →L[ℝ] ℝ} (hg : HasFDerivAt f g x) : g (z-x) ≤ f z-f x := by
  have hc := hf.comp_affineMap (AffineMap.lineMap (k := ℝ) x z)
  have hp : HasDerivAt (AffineMap.lineMap (k := ℝ) x z : ℝ → Vec n) (z-x) 0 := by
    change HasDerivAt (fun t : ℝ => t • (z-x)+x) (z-x) 0
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (z-x)).add_const x
  have hd : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x z) (g (z-x)) 0 := by
    exact hg.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hs := hc.le_slope_of_hasDerivAt (by simpa using hx) (by simpa using hz)
    (by norm_num : (0 : ℝ) < 1) hd
  simpa [slope_def_field] using hs

/-- Two actual active convex branches already force a linear central-difference
lower bound. No differentiability of the maximum at the tie is assumed. -/
theorem active_gap_central_lower {n : ℕ} {F f h : Vec n → ℝ} {U : Set (Vec n)}
    (hf : ConvexOn ℝ U f) (hh : ConvexOn ℝ U h) (hfle : ∀ x ∈ U, f x ≤ F x)
    (hhle : ∀ x ∈ U, h x ≤ F x) {star w : Vec n} (hw : w ∈ U)
    (hfa : f w = F w) (hha : h w = F w)
    {g q : Vec n →L[ℝ] ℝ} (hg : HasFDerivAt f g w) (hq : HasFDerivAt h q w)
    (t : ℝ) (ho : RadialCertificate.outwardPoint star w t ∈ U)
    (hi : RadialCertificate.inwardPoint star w t ∈ U) :
    t*(g (w-star)-q (w-star)) ≤ RadialCertificate.centralDifference F star w t := by
  have hfo := supporting_on hf hw ho hg
  have hhi := supporting_on hh hw hi hq
  have heo : RadialCertificate.outwardPoint star w t-w = t • (w-star) := by
    unfold RadialCertificate.outwardPoint RadialCertificate.inwardPoint
    module
  have hei : RadialCertificate.inwardPoint star w t-w = -t • (w-star) := by
    unfold RadialCertificate.inwardPoint
    module
  rw [heo,map_smul,smul_eq_mul,hfa] at hfo
  rw [hei,map_smul,smul_eq_mul,hha] at hhi
  have hbo := hfle _ ho
  have hbi := hhle _ hi
  unfold RadialCertificate.centralDifference
  nlinarith

theorem no_quadratic_bound_of_linear_lower {D : ℝ → ℝ} {J : ℝ} (hJ : 0 < J)
    (hlow : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε → J*t ≤ D t) :
    ¬ ∃ C ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε → D t ≤ C*t^2 := by
  rintro ⟨C,ε,hε,hup⟩
  obtain ⟨ρ,hρ,hlo⟩ := hlow
  let t := min (min ε ρ) (J/(2*(|C|+1)))
  have ht : 0 < t := lt_min (lt_min hε hρ) (div_pos hJ (by positivity))
  have htε : t ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have htρ : t ≤ ρ := (min_le_left _ _).trans (min_le_right _ _)
  have htJ := (le_div_iff₀ (show 0 < 2*(|C|+1) by positivity)).mp
    (show t ≤ J/(2*(|C|+1)) from min_le_right _ _)
  have hb := (hlo t ht.le htρ).trans (hup t ht.le htε)
  have hc : C*t < J := by nlinarith [le_abs_self C]
  nlinarith [mul_lt_mul_of_pos_right hc ht]

theorem active_gap_forbids_central_bound {n : ℕ} {F f h : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hf : ConvexOn ℝ U f) (hh : ConvexOn ℝ U h)
    (hfle : ∀ x ∈ U, f x ≤ F x) (hhle : ∀ x ∈ U, h x ≤ F x)
    {star w : Vec n} (hw : w ∈ U) (hfa : f w = F w) (hha : h w = F w)
    {g q : Vec n →L[ℝ] ℝ} (hg : HasFDerivAt f g w) (hq : HasFDerivAt h q w)
    (hgap : q (w-star) < g (w-star)) :
    ¬ ∃ C ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
      RadialCertificate.centralDifference F star w t ≤ C*t^2 := by
  have ho : Continuous (fun t => RadialCertificate.outwardPoint star w t) := by
    unfold RadialCertificate.outwardPoint RadialCertificate.inwardPoint
    fun_prop
  have hi : Continuous (fun t => RadialCertificate.inwardPoint star w t) := by
    unfold RadialCertificate.inwardPoint
    fun_prop
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), RadialCertificate.outwardPoint star w t ∈ U ∧
      RadialCertificate.inwardPoint star w t ∈ U := by
    apply inter_mem
    · exact ho.continuousAt.eventually (by simpa [RadialCertificate.outwardPoint,RadialCertificate.inwardPoint] using hU.mem_nhds hw)
    · exact hi.continuousAt.eventually (by simpa [RadialCertificate.inwardPoint] using hU.mem_nhds hw)
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  apply no_quadratic_bound_of_linear_lower (sub_pos.mpr hgap)
  refine ⟨ρ/2,by positivity,?_⟩
  intro t ht htρ
  have hmem : t ∈ Metric.ball (0 : ℝ) ρ := by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht]
    linarith
  have hs := hball hmem
  simpa only [mul_comm] using active_gap_central_lower hf hh hfle hhle hw hfa hha hg hq t hs.1 hs.2

theorem local_central_bound_of_nested {n : ℕ} {F : Vec n → ℝ} (hF : Continuous F)
    {star w : Vec n} {b : ℝ} (hpos : F star < F w) (hupper : F w < b)
    (hc : RadialCertificate.HasNestedCentralBounds F star b) :
    ∃ C ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → t ≤ ε →
      RadialCertificate.centralDifference F star w t ≤ C*t^2 := by
  let η := (F w-F star)/2
  have hη : 0 < η := by dsimp only [η]; linarith
  obtain ⟨C,θ,hθ,hθhalf,hbound⟩ := hc η hη
  have ho : Continuous (fun t => F (RadialCertificate.outwardPoint star w t)) := by
    apply hF.comp
    unfold RadialCertificate.outwardPoint RadialCertificate.inwardPoint
    fun_prop
  have hi : Continuous (fun t => F (RadialCertificate.inwardPoint star w t)) := by
    apply hF.comp
    unfold RadialCertificate.inwardPoint
    fun_prop
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), F (RadialCertificate.outwardPoint star w t) < b ∧
      F star+η < F (RadialCertificate.inwardPoint star w t) := by
    apply inter_mem
    · exact (isOpen_lt ho continuous_const).mem_nhds
        (by simpa [RadialCertificate.outwardPoint,RadialCertificate.inwardPoint] using hupper)
    · have hh : F star+η < F (RadialCertificate.inwardPoint star w (0 : ℝ)) := by
        simp only [RadialCertificate.inwardPoint,zero_smul,sub_zero]
        dsimp only [η]
        linarith
      exact (isOpen_lt continuous_const hi).mem_nhds hh
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨C,min θ (ρ/2),lt_min hθ (by positivity),?_⟩
  intro t ht hte
  have hmem : t ∈ Metric.ball (0 : ℝ) ρ := by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht]
    have hh := hte.trans (min_le_right θ (ρ/2))
    linarith
  have hs := hball hmem
  exact hbound w t ht (hte.trans (min_le_left _ _)) hs.1.le hs.2.le

/-- A genuine active radial derivative gap inside a positive objective band
forbids RS on that sublevel. This is a certificate obstruction, not a claim
that any BFGS run fails to converge. -/
theorem active_gap_forbids_radial {n : ℕ} {F f h : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {U : Set (Vec n)}
    (hU : IsOpen U) (hf : ConvexOn ℝ U f) (hh : ConvexOn ℝ U h)
    (hfle : ∀ x ∈ U, f x ≤ F x) (hhle : ∀ x ∈ U, h x ≤ F x)
    {star w : Vec n} (hw : w ∈ U) (hfa : f w = F w) (hha : h w = F w)
    {g q : Vec n →L[ℝ] ℝ} (hg : HasFDerivAt f g w) (hq : HasFDerivAt h q w)
    (hgap : q (w-star) < g (w-star)) (hmin : ∀ x, F star ≤ F x)
    {b : ℝ} (hpos : F star < F w) (hupper : F w < b) :
    ¬ RadialCertificate.HasRadialSecantBounds F {x | F x ≤ b} star := by
  intro hRS
  apply active_gap_forbids_central_bound hU hf hh hfle hhle hw hfa hha hg hq hgap
  exact local_central_bound_of_nested (convex_continuous hF) hpos hupper
    (RadialCertificate.central_of_radial_on_sublevel hF star hmin b (hpos.trans hupper) hRS)

end BfgsVerification.FiniteMaxRadial
