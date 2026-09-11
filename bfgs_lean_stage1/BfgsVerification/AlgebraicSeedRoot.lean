import BfgsVerification.AlgebraicSeedData
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter Matrix
namespace BfgsVerification.AlgebraicSeed
open PolynomialBounds

theorem radius_pos : 0 < radius := by norm_num [radius]
theorem radius_le_one : radius ≤ 1 := by norm_num [radius]
theorem contraction_constant : 7000*radius < 1/(10:ℝ)^26 := by norm_num [radius]
theorem contraction_half : 7000*radius ≤ 1/2 := by norm_num [radius]

theorem newton_zero_small : ‖newton 0‖ < 1/(10:ℝ)^50 := by
  apply (pi_norm_lt_iff (by norm_num : 0 < 1/(10:ℝ)^50)).mpr
  intro i
  fin_cases i
  · simpa [expansion0,coeff0,words,monomial,Fin.sum_univ_succ,Real.norm_eq_abs] using constant0_small
  · simpa [expansion1,coeff1,words,monomial,Fin.sum_univ_succ,Real.norm_eq_abs] using constant1_small

theorem newton_lipschitz {x y : Vec 2} (hx : ‖x‖ ≤ radius) (hy : ‖y‖ ≤ radius) :
    ‖newton x-newton y‖ ≤ 7000*radius*‖x-y‖ := by
  have hx' : ∀ i, |x i| ≤ radius := fun i => (show |x i| ≤ ‖x‖ from norm_le_pi_norm x i).trans hx
  have hy' : ∀ i, |y i| ≤ radius := fun i => (show |y i| ≤ ‖y‖ from norm_le_pi_norm y i).trans hy
  have hr0 := radius_pos.le
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 7000*radius*‖x-y‖)).mpr
  intro i
  fin_cases i
  · change |newton x 0-newton y 0| ≤ _
    rw [expansion0,expansion0,add_sub_add_left_eq_sub]
    exact (polynomial_quadratic_abs_sub_le coeff0 words words_quadratic radius_le_one hx' hy').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coeff0_bound radius_pos.le) (norm_nonneg _))
  · change |newton x 1-newton y 1| ≤ _
    rw [expansion1,expansion1,add_sub_add_left_eq_sub]
    exact (polynomial_quadratic_abs_sub_le coeff1 words words_quadratic radius_le_one hx' hy').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coeff1_bound radius_pos.le) (norm_nonneg _))

theorem newton_maps_ball : MapsTo newton (Metric.closedBall (0 : Vec 2) radius) (Metric.closedBall 0 radius) := by
  intro x hx
  have hxn : ‖x‖ ≤ radius := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hdiff := newton_lipschitz (y := (0 : Vec 2)) hxn (by simpa only [norm_zero] using radius_pos.le)
  simp only [sub_zero] at hdiff
  have hb : ‖newton x‖ ≤ 7000*radius*radius+‖newton 0‖ := calc
    _ ≤ ‖newton x-newton 0‖+‖newton 0‖ := by simpa only [add_comm,norm_sub_rev] using norm_le_insert (newton 0) (newton x)
    _ ≤ 7000*radius*radius+‖newton 0‖ := add_le_add_right
      (hdiff.trans (mul_le_mul_of_nonneg_left hxn (by have := radius_pos; positivity))) _
  have he : 7000*radius*radius+1/(10:ℝ)^50 < radius := by norm_num [radius]
  have hh := add_lt_add_left newton_zero_small (7000*radius*radius)
  simpa only [Metric.mem_closedBall,dist_zero_right] using (hb.trans_lt (hh.trans he)).le

theorem newton_contracting : ContractingWith (1/2 : ℝ≥0)
    (newton_maps_ball.restrict newton (Metric.closedBall 0 radius) (Metric.closedBall 0 radius)) := by
  refine ⟨by change (1/2:ℝ)<1; norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  change dist (newton x.val) (newton y.val) ≤ ((1/2 : ℝ≥0):ℝ)*dist x.val y.val
  rw [dist_eq_norm,dist_eq_norm]
  have hx : ‖x.val‖ ≤ radius := by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
  have hy : ‖y.val‖ ≤ radius := by simpa only [Metric.mem_closedBall,dist_zero_right] using y.property
  exact (newton_lipschitz hx hy).trans (mul_le_mul_of_nonneg_right
    (by simpa only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using contraction_half) (norm_nonneg _))

theorem fixed_iff_root (x : Vec 2) : newton x=x ↔ P (center+x)=0 := by
  constructor
  · intro hx
    have hm : M.mulVec (P (center+x))=0 := sub_eq_self.mp hx
    have he := congrArg (J.mulVec) hm
    rw [mulVec_mulVec,Matrix.mul_eq_one_comm.mp M_left_inverse,one_mulVec,mulVec_zero] at he
    exact he
  · intro hx
    simp only [newton,hx,mulVec_zero,sub_zero]

theorem fixed_unique {x y : Vec 2} (hx : ‖x‖ ≤ radius) (hy : ‖y‖ ≤ radius)
    (hfx : newton x=x) (hfy : newton y=y) : x=y := by
  have hh := newton_lipschitz hx hy
  rw [hfx,hfy] at hh
  have hb : ‖x-y‖ ≤ (1/2)*‖x-y‖ := hh.trans (mul_le_mul_of_nonneg_right contraction_half (norm_nonneg _))
  have hz : ‖x-y‖=0 := by linarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem exists_unique_root : ∃! x : Vec 2, ‖x-center‖ ≤ radius ∧ P x=0 := by
  obtain ⟨v,hv,hfix,_⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete newton_maps_ball newton_contracting
    (Metric.mem_closedBall_self radius_pos.le) (edist_ne_top (0 : Vec 2) (newton 0))
  have hvn : ‖v‖ ≤ radius := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  refine ⟨center+v,⟨?_,(fixed_iff_root v).mp hfix⟩,?_⟩
  · simpa only [add_sub_cancel_left] using hvn
  · intro x hx
    have he : center+(x-center)=x := add_sub_cancel _ _
    have hf : newton (x-center)=x-center := (fixed_iff_root _).mpr (by rw [he]; exact hx.2)
    have hh := fixed_unique hx.1 hvn hf hfix
    calc
      x = center+(x-center) := he.symm
      _ = center+v := congrArg (center+·) hh

noncomputable def root : Vec 2 := Classical.choose exists_unique_root

theorem root_spec : ‖root-center‖ ≤ radius ∧ P root=0 := (Classical.choose_spec exists_unique_root).1

theorem root_unique (x : Vec 2) (hx : ‖x-center‖ ≤ radius ∧ P x=0) : x=root :=
  (Classical.choose_spec exists_unique_root).2 x hx

theorem exact_closed_box : ∃! x : Vec 2,
    (∀ i, |x i-center i| ≤ 1/(10:ℝ)^30) ∧
      264192*R (x 0) (x 1)*K (x 0) (x 1)-U (x 0) (x 1)*V (x 0) (x 1)*(U (x 0) (x 1)+129)=0 ∧
      16*V (x 0) (x 1)*T (x 0) (x 1)*K (x 0) (x 1)-R (x 0) (x 1)*U (x 0) (x 1)*Y (x 0) (x 1)=0 := by
  have he (x : Vec 2) : (‖x-center‖ ≤ radius ∧ P x=0) ↔
      (∀ i, |x i-center i| ≤ 1/(10:ℝ)^30) ∧
      264192*R (x 0) (x 1)*K (x 0) (x 1)-U (x 0) (x 1)*V (x 0) (x 1)*(U (x 0) (x 1)+129)=0 ∧
      16*V (x 0) (x 1)*T (x 0) (x 1)*K (x 0) (x 1)-R (x 0) (x 1)*U (x 0) (x 1)*Y (x 0) (x 1)=0 := by
    rw [pi_norm_le_iff_of_nonneg radius_pos.le]
    simp only [Pi.sub_apply,Real.norm_eq_abs,radius,P,funext_iff,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Pi.zero_apply]
  simpa only [← he] using exists_unique_root


theorem box_coarse {x : Vec 2} (hx : ‖x-center‖ ≤ radius) :
    (318/1000:ℝ) < x 0 ∧ x 0 < 319/1000 ∧
      (-1026/1000:ℝ) < x 1 ∧ x 1 < -1025/1000 := by
  have hc : |x 0-center 0| ≤ radius := (show |x 0-center 0| ≤ ‖x-center‖ from norm_le_pi_norm (x-center) 0).trans hx
  have hd : |x 1-center 1| ≤ radius := (show |x 1-center 1| ≤ ‖x-center‖ from norm_le_pi_norm (x-center) 1).trans hx
  have hca := abs_le.mp hc
  have hda := abs_le.mp hd
  norm_num [center,radius] at hca hda
  constructor
  · linarith [hca.1]
  constructor
  · linarith [hca.2]
  constructor
  · linarith [hda.1]
  · linarith [hda.2]

def ratio (c d : ℝ) : ℝ := 129*R c d/(V c d*(U c d+129))

theorem coarse_factors {c d : ℝ}
    (hc : (318/1000:ℝ) < c) (hc' : c < 319/1000)
    (hd : (-1026/1000:ℝ) < d) (hd' : d < -1025/1000) :
    0 < U c d ∧ 0 < V c d ∧ 0 < R c d ∧ 0 < K c d ∧
      0 < T c d ∧ 0 < Y c d ∧ 0 < U c d+129 := by
  have hc2 : (318/1000:ℝ)^2 < c^2 := by nlinarith [sq_nonneg (c-318/1000)]
  have hd2 : (1025/1000:ℝ)^2 < d^2 := by nlinarith [sq_nonneg (d+1025/1000)]
  dsimp [U,V,R,K,T,Y]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg (c-1)]

theorem coarse_ratio {c d : ℝ}
    (hc : (318/1000:ℝ) < c) (hc' : c < 319/1000)
    (hd : (-1026/1000:ℝ) < d) (hd' : d < -1025/1000) :
    (60/1000:ℝ) < ratio c d ∧ ratio c d < 61/1000 := by
  have hU : (2397/100:ℝ) ≤ U c d ∧ U c d ≤ 24113/1000 := by dsimp [U]; constructor <;> linarith
  have hV : (119263/1000:ℝ) ≤ V c d ∧ V c d ≤ 59703/500 := by dsimp [V]; constructor <;> linarith
  have hR : (4259/500:ℝ) ≤ R c d ∧ R c d ≤ 8527/1000 := by dsimp [R]; constructor <;> linarith
  have hpos := coarse_factors hc hc' hd hd'
  have hden : 0 < V c d*(U c d+129) := mul_pos hpos.2.1 hpos.2.2.2.2.2.2
  have hlo : (119263/1000:ℝ)*(2397/100+129) ≤ V c d*(U c d+129) :=
    mul_le_mul hV.1 (add_le_add_right hU.1 _) (by norm_num) hpos.2.1.le
  have hhi : V c d*(U c d+129) ≤ (59703/500:ℝ)*(24113/1000+129) :=
    mul_le_mul hV.2 (add_le_add_right hU.2 _) hpos.2.2.2.2.2.2.le (by norm_num)
  dsimp [ratio]
  constructor
  · apply (lt_div_iff₀ hden).mpr
    nlinarith [hR.1]
  · apply (div_lt_iff₀ hden).mpr
    nlinarith [hR.2]

theorem box_denominators_and_ratio {x : Vec 2} (hx : ‖x-center‖ ≤ radius) :
    0 < U (x 0) (x 1) ∧ 0 < V (x 0) (x 1) ∧ 0 < R (x 0) (x 1) ∧
      0 < K (x 0) (x 1) ∧ 0 < T (x 0) (x 1) ∧ 0 < Y (x 0) (x 1) ∧
      0 < U (x 0) (x 1)+129 ∧
      (60/1000:ℝ) < ratio (x 0) (x 1) ∧ ratio (x 0) (x 1) < 61/1000 := by
  obtain ⟨hc,hc',hd,hd'⟩ := box_coarse hx
  have hf := coarse_factors hc hc' hd hd'
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2.1,
    hf.2.2.2.2.2.2,coarse_ratio hc hc' hd hd'⟩

end BfgsVerification.AlgebraicSeed
