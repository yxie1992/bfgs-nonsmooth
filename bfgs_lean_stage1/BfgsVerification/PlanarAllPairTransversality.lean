import BfgsVerification.PlanarRunTransversality

noncomputable section
open scoped BigOperators Topology ContDiff NNReal
open Set Filter Matrix Metric
namespace BfgsVerification.PlanarAllPairs
open HomogeneousPlanar PlanarTransversality PlanarNormalGeometry ConvexSubdifferential TransportedCertificate

variable {F : Vec 2 → ℝ} {c₁ c₂ : ℝ} {x z g h : Vec 2}

theorem eligible_step_ne_zero (hp : EligiblePair F c₁ c₂ x z g h) : z-x≠0 := by
  intro hz
  have hd := hp.decrease_pos
  change 0 < -dot g (z-x) at hd
  rw [hz] at hd
  norm_num [dot] at hd

theorem eligible_normalized_descent (hp : EligiblePair F c₁ c₂ x z g h) :
    dot g (normalized (z-x)) ≤ 0 := by
  have hd : dot g (z-x) < 0 := by simpa only [pairDecrease,pairStep,neg_pos] using hp.decrease_pos
  rw [normalized,dot_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) hd.le

theorem eligible_normalized_wolfe (hp : EligiblePair F c₁ c₂ x z g h) :
    (1-c₂)*(-dot g (normalized (z-x))) ≤ dot (h-g) (normalized (z-x)) := by
  have hc := mul_le_mul_of_nonneg_left hp.curvature
    (inv_nonneg.mpr (norm_nonneg (euclideanVector (z-x))))
  rw [normalized,dot_smul_right,dot_smul_right]
  convert hc using 1 <;> dsimp [pairDecrease,pairStep,pairCurvature] <;> ring

/-- Compact all-pair transversality. Endpoints are arbitrary actual eligible
pairs, unrelated to any common trajectory or matrix sequence. -/
theorem compact_pair_transversality (hF : ConvexOn ℝ univ F) {Q : Set (Vec 2)}
    (hQ : IsCompact Q) (hc₂ : c₂ < 1) (W : Vec 2 → Vec 2)
    (hW : ∀p∈Q,ContinuousAt W p)
    (hpos : ∀p∈Q,∀a∈subdifferential F p,0 < dot a (W p))
    (hcommon : ∀p∈Q,∀a∈subdifferential F p,∀b∈subdifferential F p,dot a (W p)=dot b (W p)) :
    ∃κ : ℝ,0 < κ ∧ ∃δ : ℝ,0 < δ ∧ ∀x∈Q,∀z∈Q,∀g h,
      EligiblePair F c₁ c₂ x z g h → ‖z-x‖ < δ → ∀θ∈Icc (0 : ℝ) 1,
        κ ≤ |pairDet (normalized (z-x)) (W (x+θ • (z-x)))| := by
  classical
  by_contra hn
  push_neg at hn
  have hc (j : ℕ) : ∃x∈Q,∃z∈Q,∃g h,
      EligiblePair F c₁ c₂ x z g h ∧ ‖z-x‖ < 1/((j : ℝ)+1) ∧
      ∃θ∈Icc (0 : ℝ) 1,|pairDet (normalized (z-x)) (W (x+θ • (z-x)))| < 1/((j : ℝ)+1) :=
    hn (1/((j : ℝ)+1)) (by positivity) (1/((j : ℝ)+1)) (by positivity)
  choose x hx z hz g h hp hsmall θ hθ hbad using hc
  obtain ⟨G,hG,hbound⟩ := convex_gradient_bound_on_compact hF hQ
  let C : Set (Vec 2 × Vec 2 × Vec 2 × Vec 2 × ℝ) :=
    Q ×ˢ closedBall (0 : Vec 2) G ×ˢ closedBall (0 : Vec 2) G ×ˢ
      CertificateGeometry.euclideanUnitBall ×ˢ Icc (0 : ℝ) 1
  have hC : IsCompact C := hQ.prod ((isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (CertificateGeometry.euclideanUnitBall_compact.prod isCompact_Icc)))
  let sample (j : ℕ) := (x j,g j,h j,normalized (z j-x j),θ j)
  have hsample (j : ℕ) : sample j∈C := by
    refine ⟨hx j,?_,?_,?_,hθ j⟩
    · rw [mem_closedBall,dist_zero_right]
      exact norm_le_of_sqNorm_le hG.le (hbound _ (hx j) _ (hp j).gradient_x)
    · rw [mem_closedBall,dist_zero_right]
      exact norm_le_of_sqNorm_le hG.le (hbound _ (hz j) _ (hp j).gradient_z)
    · exact (PlanarObjectiveField.normalized_sqNorm (eligible_step_ne_zero (hp j))).le
  obtain ⟨limit,hlimit,φ,hφ,hconv⟩ := hC.tendsto_subseq hsample
  let p := limit.1
  let g0 := limit.2.1
  let g1 := limit.2.2.1
  let e := limit.2.2.2.1
  let angle := limit.2.2.2.2
  have hxp : Tendsto (fun j => x (φ j)) atTop (𝓝 p) := (continuous_fst.tendsto limit).comp hconv
  have hgp : Tendsto (fun j => g (φ j)) atTop (𝓝 g0) :=
    ((continuous_fst.comp continuous_snd).tendsto limit).comp hconv
  have hhp : Tendsto (fun j => h (φ j)) atTop (𝓝 g1) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto limit).comp hconv
  have hep : Tendsto (fun j => normalized (z (φ j)-x (φ j))) atTop (𝓝 e) :=
    ((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).tendsto limit).comp hconv
  have hθp : Tendsto (fun j => θ (φ j)) atTop (𝓝 angle) :=
    ((continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).tendsto limit).comp hconv
  have hstep : Tendsto (fun j => z j-x j) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => (hsmall j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hs := hstep.comp hφ.tendsto_atTop
  have hzp : Tendsto (fun j => z (φ j)) atTop (𝓝 p) := by
    have heq (j : ℕ) : x (φ j)+(z (φ j)-x (φ j))=z (φ j) := by abel
    simpa only [Function.comp_def,heq,add_zero] using hxp.add hs
  have hg0 : g0∈subdifferential F p := (isClosed_graph (convex_continuous hF)).mem_of_tendsto
    (hxp.prodMk_nhds hgp) (Eventually.of_forall (fun j => convex_supporting_inequality hF (hp (φ j)).gradient_x))
  have hg1 : g1∈subdifferential F p := (isClosed_graph (convex_continuous hF)).mem_of_tendsto
    (hzp.prodMk_nhds hhp) (Eventually.of_forall (fun j => convex_supporting_inequality hF (hp (φ j)).gradient_z))
  have heunit : sqNorm e=1 := by
    have hl := continuous_sqNorm.tendsto e |>.comp hep
    have hone : Tendsto (fun j => sqNorm (normalized (z (φ j)-x (φ j)))) atTop (𝓝 (1 : ℝ)) := by
      simpa only [PlanarObjectiveField.normalized_sqNorm (eligible_step_ne_zero (hp _))] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hl hone
  have hene : e≠0 := by intro hez; simp [hez,sqNorm] at heunit
  have hmid : Tendsto (fun j => x (φ j)+θ (φ j) • (z (φ j)-x (φ j))) atTop (𝓝 p) := by
    simpa only [smul_zero,add_zero] using hxp.add (hθp.smul hs)
  have hw := (hW p hlimit.1).tendsto.comp hmid
  have hdet : pairDet e (W p)≠0 := limiting_determinant_ne_zero
    (fun j => g (φ j)) (fun j => h (φ j)) (fun j => normalized (z (φ j)-x (φ j)))
    (fun j => W (x (φ j)+θ (φ j) • (z (φ j)-x (φ j))))
    hgp hhp hep hw (sub_pos.mpr hc₂) hene (hpos p hlimit.1 g0 hg0)
    (hcommon p hlimit.1 g0 hg0 g1 hg1)
    (Eventually.of_forall (fun j => eligible_normalized_descent (hp (φ j))))
    (Eventually.of_forall (fun j => eligible_normalized_wolfe (hp (φ j))))
  have hdetlim : Tendsto (fun j => |pairDet (normalized (z (φ j)-x (φ j)))
      (W (x (φ j)+θ (φ j) • (z (φ j)-x (φ j))))|) atTop (𝓝 |pairDet e (W p)|) := by
    have hc : Continuous (fun v : Vec 2 × Vec 2 => |pairDet v.1 v.2|) := by unfold pairDet; fun_prop
    exact (hc.tendsto _).comp (hep.prodMk_nhds hw)
  have hzero : Tendsto (fun j => |pairDet (normalized (z (φ j)-x (φ j)))
      (W (x (φ j)+θ (φ j) • (z (φ j)-x (φ j))))|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun j => (hbad (φ j)).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  exact hdet (abs_eq_zero.mp (tendsto_nhds_unique hdetlim hzero))

theorem compact_pair_transversality_length (hF : ConvexOn ℝ univ F) {Q : Set (Vec 2)}
    (hQ : IsCompact Q) (hc₂ : c₂ < 1) (W : Vec 2 → Vec 2)
    (hW : ∀p∈Q,ContinuousAt W p)
    (hpos : ∀p∈Q,∀a∈subdifferential F p,0 < dot a (W p))
    (hcommon : ∀p∈Q,∀a∈subdifferential F p,∀b∈subdifferential F p,dot a (W p)=dot b (W p)) :
    ∃κ : ℝ,0 < κ ∧ ∃δ : ℝ,0 < δ ∧ ∀x∈Q,∀z∈Q,∀g h,
      EligiblePair F c₁ c₂ x z g h → ‖z-x‖ < δ → ∀θ∈Icc (0 : ℝ) 1,
        κ*‖euclideanVector (z-x)‖ ≤ |pairDet (z-x) (W (x+θ • (z-x)))| := by
  obtain ⟨κ,hκ,δ,hδ,hb⟩ := compact_pair_transversality hF hQ hc₂ W hW hpos hcommon
  refine ⟨κ,hκ,δ,hδ,?_⟩
  intro x hx z hz g h hp hs θ hθ
  have hn : 0 < ‖euclideanVector (z-x)‖ := by
    apply norm_pos_iff.mpr
    intro he
    exact eligible_step_ne_zero hp (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => fun i => v i) he)
  have he : pairDet (normalized (z-x)) (W (x+θ • (z-x)))=
      ‖euclideanVector (z-x)‖⁻¹*pairDet (z-x) (W (x+θ • (z-x))) := by
    simp only [pairDet,normalized,Pi.smul_apply,smul_eq_mul]
    ring
  have hh := hb x hx z hz g h hp hs θ hθ
  rw [he,abs_mul,abs_inv,abs_of_pos hn] at hh
  apply (le_div_iff₀ hn).mp
  simpa only [div_eq_mul_inv,mul_comm] using hh

end BfgsVerification.PlanarAllPairs
