import BfgsVerification.AlgebraicSeedOracleData
noncomputable section
set_option maxHeartbeats 1000000
namespace BfgsVerification.SeedOrbit
open IntervalBounds AlgebraicSeed

theorem base_0_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    PointCertificate c d (point c d r 0) 0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := raw_base_0 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨?_,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]

theorem base_1_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    PointCertificate c d (point c d r 1) 1 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := raw_base_1 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨?_,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]

theorem base_2_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    PointCertificate c d (point c d r 2) 2 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := raw_base_2 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨?_,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
    · exact False.elim (hk rfl)
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]

theorem trial_0_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 0 (1 : ℝ) 1 true := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := raw_trial_0 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro _
    norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h12]

theorem trial_1_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 1 (1 : ℝ) 0 false := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := raw_trial_1 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro h
    cases h

theorem trial_2_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 1 (1/2 : ℝ) 0 false := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := raw_trial_2 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro h
    cases h

theorem trial_3_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 1 (1/4 : ℝ) 2 true := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := raw_trial_3 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
    · exact False.elim (hk rfl)
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro _
    norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h12]

theorem trial_4_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 2 (1 : ℝ) 0 false := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := raw_trial_4 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro h
    cases h

theorem trial_5_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 2 (1/2 : ℝ) 0 false := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := raw_trial_5 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro h
    cases h

theorem trial_6_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 2 (1/4 : ℝ) 0 false := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := raw_trial_6 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro h
    cases h

theorem trial_7_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 2 (1/8 : ℝ) 0 false := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := raw_trial_7 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro h
    cases h

theorem trial_8_certificate {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    TrialCertificate c d r 2 (1/16 : ℝ) 0 true := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := raw_trial_8 hc hd hr
  norm_num [div_eq_mul_inv] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro k hk
    fin_cases k
    · exact False.elim (hk rfl)
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h0]
    · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h1]
  · intro k
    fin_cases k
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h2,h3]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h4,h5]
    · apply abs_lt.mpr
      constructor <;> norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h6,h7]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h8]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h9]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h11]
  · norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h10]
  · intro _
    norm_num [trial,point,initialPoint,direction,gradient,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,dot,Fin.sum_univ_two,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,div_eq_mul_inv] <;> nlinarith only [h12]

end BfgsVerification.SeedOrbit
