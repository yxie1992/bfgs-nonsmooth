import BfgsVerification.LShapeDerivative
import BfgsVerification.LShapeIntervalTools
noncomputable section
open Matrix
namespace BfgsVerification.LShapeIntervalCertificate
open IntervalBounds LShapeIntervalTools LShapeDerivative
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000


theorem column_0_bounds {c d : ℝ}
    (hc : Bounds (318481427627118/10^15) c (318481427627119/10^15))
    (hd : Bounds (-1025232119675749/10^15) d (-1025232119675748/10^15)) :
    Bounds (11123986249/10000000000 : ℝ) (jacobian c d 0 0) (11123986253/10000000000 : ℝ) ∧
    Bounds (7515015701/10000000000 : ℝ) (jacobian c d 1 0) (1878753927/2500000000 : ℝ) := by

  obtain ⟨j0,hj0⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (1 : ℝ)=z := ⟨_,rfl⟩
  have j0_value : Bounds (1 : ℝ) j0.value (1 : ℝ) := by
    simpa only [← hj0,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (1 : ℝ))
  have j0_tangent : Bounds (0 : ℝ) j0.tangent (0 : ℝ) := by
    simpa only [← hj0,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j1,hj1⟩ : ∃ z : LReturnJets.Jet, ⟨(0 : ℝ),(1 : ℝ)⟩=z := ⟨_,rfl⟩
  have j1_value : Bounds (0 : ℝ) j1.value (0 : ℝ) := by
    simpa only [← hj1] using (IntervalBounds.exact (0 : ℝ))
  have j1_tangent : Bounds (1 : ℝ) j1.tangent (1 : ℝ) := by
    simpa only [← hj1] using (IntervalBounds.exact (1 : ℝ))
  obtain ⟨j2,hj2⟩ : ∃ z : LReturnJets.Jet, ⟨(1 : ℝ),(0 : ℝ)⟩=z := ⟨_,rfl⟩
  have j2_value : Bounds (1 : ℝ) j2.value (1 : ℝ) := by
    simpa only [← hj2] using (IntervalBounds.exact (1 : ℝ))
  have j2_tangent : Bounds (0 : ℝ) j2.tangent (0 : ℝ) := by
    simpa only [← hj2] using (IntervalBounds.exact (0 : ℝ))
  have hm00 : jetIter c d 0 0=!![j0,j1;j1,j2] := by
    simp only [← hj0,← hj1,← hj2]
    rfl
  let v0 : ℝ := -(1 : ℝ)
  have h0 : Bounds (-1 : ℝ) v0 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (1 : ℝ))) (by norm_num) (by norm_num)
  let v1 : ℝ := (-1 : ℝ)+v0
  have h1 : Bounds (-2 : ℝ) v1 (-2 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (-1 : ℝ)) h0) (by norm_num) (by norm_num)
  obtain ⟨j3,hj3⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((-1 : ℝ)+(-(1 : ℝ)))=z := ⟨_,rfl⟩
  have j3_value : Bounds (-2 : ℝ) j3.value (-2 : ℝ) := by
    simpa only [← hj3,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h1
  have j3_tangent : Bounds (0 : ℝ) j3.tangent (0 : ℝ) := by
    simpa only [← hj3,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j4,hj4⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1 : ℝ)=z := ⟨_,rfl⟩
  have j4_value : Bounds (-1 : ℝ) j4.value (-1 : ℝ) := by
    simpa only [← hj4,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1 : ℝ))
  have j4_tangent : Bounds (0 : ℝ) j4.tangent (0 : ℝ) := by
    simpa only [← hj4,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v2 : ℝ := j0.value*j0.value
  have h2 : Bounds (1 : ℝ) v2 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j0_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v3 : ℝ := j0.tangent*j0.value
  have h3 : Bounds (0 : ℝ) v3 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j0_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v4 : ℝ := j0.value*j0.tangent
  have h4 : Bounds (0 : ℝ) v4 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j0_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v5 : ℝ := v3+v4
  have h5 : Bounds (0 : ℝ) v5 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h3 h4) (by norm_num) (by norm_num)
  obtain ⟨j5,hj5⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j0 j0=z := ⟨_,rfl⟩
  have j5_value : Bounds (1 : ℝ) j5.value (1 : ℝ) := by
    simpa only [← hj5,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h2
  have j5_tangent : Bounds (0 : ℝ) j5.tangent (0 : ℝ) := by
    simpa only [← hj5,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h5
  obtain ⟨j6,hj6⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (0 : ℝ)=z := ⟨_,rfl⟩
  have j6_value : Bounds (0 : ℝ) j6.value (0 : ℝ) := by
    simpa only [← hj6,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  have j6_tangent : Bounds (0 : ℝ) j6.tangent (0 : ℝ) := by
    simpa only [← hj6,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v6 : ℝ := j1.value*j6.value
  have h6 : Bounds (0 : ℝ) v6 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v7 : ℝ := j1.tangent*j6.value
  have h7 : Bounds (0 : ℝ) v7 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_tangent j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v8 : ℝ := j1.value*j6.tangent
  have h8 : Bounds (0 : ℝ) v8 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j6_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v9 : ℝ := v7+v8
  have h9 : Bounds (0 : ℝ) v9 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h7 h8) (by norm_num) (by norm_num)
  obtain ⟨j7,hj7⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j1 j6=z := ⟨_,rfl⟩
  have j7_value : Bounds (0 : ℝ) j7.value (0 : ℝ) := by
    simpa only [← hj7,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h6
  have j7_tangent : Bounds (0 : ℝ) j7.tangent (0 : ℝ) := by
    simpa only [← hj7,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h9
  let v10 : ℝ := j5.value+j7.value
  have h10 : Bounds (1 : ℝ) v10 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j5_value j7_value) (by norm_num) (by norm_num)
  let v11 : ℝ := j5.tangent+j7.tangent
  have h11 : Bounds (0 : ℝ) v11 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j5_tangent j7_tangent) (by norm_num) (by norm_num)
  obtain ⟨j8,hj8⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j5 j7=z := ⟨_,rfl⟩
  have j8_value : Bounds (1 : ℝ) j8.value (1 : ℝ) := by
    simpa only [← hj8,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h10
  have j8_tangent : Bounds (0 : ℝ) j8.tangent (0 : ℝ) := by
    simpa only [← hj8,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h11
  let v12 : ℝ := j4.value*j8.value
  have h12 : Bounds (-1 : ℝ) v12 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j8_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v13 : ℝ := j4.tangent*j8.value
  have h13 : Bounds (0 : ℝ) v13 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j4_tangent j8_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v14 : ℝ := j4.value*j8.tangent
  have h14 : Bounds (0 : ℝ) v14 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j8_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v15 : ℝ := v13+v14
  have h15 : Bounds (0 : ℝ) v15 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h13 h14) (by norm_num) (by norm_num)
  obtain ⟨j9,hj9⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j4 j8=z := ⟨_,rfl⟩
  have j9_value : Bounds (-1 : ℝ) j9.value (-1 : ℝ) := by
    simpa only [← hj9,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h12
  have j9_tangent : Bounds (0 : ℝ) j9.tangent (0 : ℝ) := by
    simpa only [← hj9,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h15
  let v16 : ℝ := j3.value*j9.value
  have h16 : Bounds (2 : ℝ) v16 (2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j3_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v17 : ℝ := j3.tangent*j9.value
  have h17 : Bounds (0 : ℝ) v17 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j3_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v18 : ℝ := j3.value*j9.tangent
  have h18 : Bounds (0 : ℝ) v18 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j3_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v19 : ℝ := v17+v18
  have h19 : Bounds (0 : ℝ) v19 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h17 h18) (by norm_num) (by norm_num)
  obtain ⟨j10,hj10⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j3 j9=z := ⟨_,rfl⟩
  have j10_value : Bounds (2 : ℝ) j10.value (2 : ℝ) := by
    simpa only [← hj10,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h16
  have j10_tangent : Bounds (0 : ℝ) j10.tangent (0 : ℝ) := by
    simpa only [← hj10,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h19
  let v20 : ℝ := -(0 : ℝ)
  have h20 : Bounds (0 : ℝ) v20 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (0 : ℝ))) (by norm_num) (by norm_num)
  let v21 : ℝ := (-1/8 : ℝ)+v20
  have h21 : Bounds (-1/8 : ℝ) v21 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (-1/8 : ℝ)) h20) (by norm_num) (by norm_num)
  obtain ⟨j11,hj11⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((-1/8 : ℝ)+(-(0 : ℝ)))=z := ⟨_,rfl⟩
  have j11_value : Bounds (-1/8 : ℝ) j11.value (-1/8 : ℝ) := by
    simpa only [← hj11,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h21
  have j11_tangent : Bounds (0 : ℝ) j11.tangent (0 : ℝ) := by
    simpa only [← hj11,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v22 : ℝ := j1.value*j0.value
  have h22 : Bounds (0 : ℝ) v22 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v23 : ℝ := j1.tangent*j0.value
  have h23 : Bounds (1 : ℝ) v23 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v24 : ℝ := j1.value*j0.tangent
  have h24 : Bounds (0 : ℝ) v24 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v25 : ℝ := v23+v24
  have h25 : Bounds (1 : ℝ) v25 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h23 h24) (by norm_num) (by norm_num)
  obtain ⟨j12,hj12⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j1 j0=z := ⟨_,rfl⟩
  have j12_value : Bounds (0 : ℝ) j12.value (0 : ℝ) := by
    simpa only [← hj12,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h22
  have j12_tangent : Bounds (1 : ℝ) j12.tangent (1 : ℝ) := by
    simpa only [← hj12,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h25
  let v26 : ℝ := j2.value*j6.value
  have h26 : Bounds (0 : ℝ) v26 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j2_value j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v27 : ℝ := j2.tangent*j6.value
  have h27 : Bounds (0 : ℝ) v27 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j2_tangent j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v28 : ℝ := j2.value*j6.tangent
  have h28 : Bounds (0 : ℝ) v28 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j2_value j6_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v29 : ℝ := v27+v28
  have h29 : Bounds (0 : ℝ) v29 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h27 h28) (by norm_num) (by norm_num)
  obtain ⟨j13,hj13⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j2 j6=z := ⟨_,rfl⟩
  have j13_value : Bounds (0 : ℝ) j13.value (0 : ℝ) := by
    simpa only [← hj13,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h26
  have j13_tangent : Bounds (0 : ℝ) j13.tangent (0 : ℝ) := by
    simpa only [← hj13,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h29
  let v30 : ℝ := j12.value+j13.value
  have h30 : Bounds (0 : ℝ) v30 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j12_value j13_value) (by norm_num) (by norm_num)
  let v31 : ℝ := j12.tangent+j13.tangent
  have h31 : Bounds (1 : ℝ) v31 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j12_tangent j13_tangent) (by norm_num) (by norm_num)
  obtain ⟨j14,hj14⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j12 j13=z := ⟨_,rfl⟩
  have j14_value : Bounds (0 : ℝ) j14.value (0 : ℝ) := by
    simpa only [← hj14,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h30
  have j14_tangent : Bounds (1 : ℝ) j14.tangent (1 : ℝ) := by
    simpa only [← hj14,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h31
  let v32 : ℝ := j4.value*j14.value
  have h32 : Bounds (0 : ℝ) v32 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j14_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v33 : ℝ := j4.tangent*j14.value
  have h33 : Bounds (0 : ℝ) v33 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j4_tangent j14_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v34 : ℝ := j4.value*j14.tangent
  have h34 : Bounds (-1 : ℝ) v34 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j14_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v35 : ℝ := v33+v34
  have h35 : Bounds (-1 : ℝ) v35 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.add h33 h34) (by norm_num) (by norm_num)
  obtain ⟨j15,hj15⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j4 j14=z := ⟨_,rfl⟩
  have j15_value : Bounds (0 : ℝ) j15.value (0 : ℝ) := by
    simpa only [← hj15,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h32
  have j15_tangent : Bounds (-1 : ℝ) j15.tangent (-1 : ℝ) := by
    simpa only [← hj15,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h35
  let v36 : ℝ := j11.value*j15.value
  have h36 : Bounds (0 : ℝ) v36 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j11_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v37 : ℝ := j11.tangent*j15.value
  have h37 : Bounds (0 : ℝ) v37 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j11_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v38 : ℝ := j11.value*j15.tangent
  have h38 : Bounds (1/8 : ℝ) v38 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j11_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v39 : ℝ := v37+v38
  have h39 : Bounds (1/8 : ℝ) v39 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add h37 h38) (by norm_num) (by norm_num)
  obtain ⟨j16,hj16⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j11 j15=z := ⟨_,rfl⟩
  have j16_value : Bounds (0 : ℝ) j16.value (0 : ℝ) := by
    simpa only [← hj16,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h36
  have j16_tangent : Bounds (1/8 : ℝ) j16.tangent (1/8 : ℝ) := by
    simpa only [← hj16,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h39
  let v40 : ℝ := j10.value+j16.value
  have h40 : Bounds (2 : ℝ) v40 (2 : ℝ) := by
    exact enlarge (IntervalBounds.add j10_value j16_value) (by norm_num) (by norm_num)
  let v41 : ℝ := j10.tangent+j16.tangent
  have h41 : Bounds (1/8 : ℝ) v41 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add j10_tangent j16_tangent) (by norm_num) (by norm_num)
  obtain ⟨j17,hj17⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j10 j16=z := ⟨_,rfl⟩
  have j17_value : Bounds (2 : ℝ) j17.value (2 : ℝ) := by
    simpa only [← hj17,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h40
  have j17_tangent : Bounds (1/8 : ℝ) j17.tangent (1/8 : ℝ) := by
    simpa only [← hj17,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h41
  let v42 : ℝ := j17.value⁻¹
  have h42 : Bounds (1/2 : ℝ) v42 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j17_value (by norm_num)) (by norm_num) (by norm_num)
  let v43 : ℝ := -j17.tangent
  have h43 : Bounds (-1/8 : ℝ) v43 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.neg j17_tangent) (by norm_num) (by norm_num)
  let v44 : ℝ := j17.value*j17.value
  have h44 : Bounds (4 : ℝ) v44 (4 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j17_value j17_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v45 : ℝ := v44⁻¹
  have h45 : Bounds (1/4 : ℝ) v45 (1/4 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h44 (by norm_num)) (by norm_num) (by norm_num)
  let v46 : ℝ := v43*v45
  have h46 : Bounds (-1/32 : ℝ) v46 (-1/32 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn h43 h45 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j18,hj18⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j17=z := ⟨_,rfl⟩
  have j18_value : Bounds (1/2 : ℝ) j18.value (1/2 : ℝ) := by
    simpa only [← hj18,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h42
  have j18_tangent : Bounds (-1/32 : ℝ) j18.tangent (-1/32 : ℝ) := by
    simpa only [← hj18,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h46
  let v47 : ℝ := j9.value*j3.value
  have h47 : Bounds (2 : ℝ) v47 (2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j9_value j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v48 : ℝ := j9.tangent*j3.value
  have h48 : Bounds (0 : ℝ) v48 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j9_tangent j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v49 : ℝ := j9.value*j3.tangent
  have h49 : Bounds (0 : ℝ) v49 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j3_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v50 : ℝ := v48+v49
  have h50 : Bounds (0 : ℝ) v50 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h48 h49) (by norm_num) (by norm_num)
  obtain ⟨j19,hj19⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j3=z := ⟨_,rfl⟩
  have j19_value : Bounds (2 : ℝ) j19.value (2 : ℝ) := by
    simpa only [← hj19,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h47
  have j19_tangent : Bounds (0 : ℝ) j19.tangent (0 : ℝ) := by
    simpa only [← hj19,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h50
  let v51 : ℝ := j18.value*j19.value
  have h51 : Bounds (1 : ℝ) v51 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j19_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v52 : ℝ := j18.tangent*j19.value
  have h52 : Bounds (-1/16 : ℝ) v52 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j19_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v53 : ℝ := j18.value*j19.tangent
  have h53 : Bounds (0 : ℝ) v53 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j19_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v54 : ℝ := v52+v53
  have h54 : Bounds (-1/16 : ℝ) v54 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h52 h53) (by norm_num) (by norm_num)
  obtain ⟨j20,hj20⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j19=z := ⟨_,rfl⟩
  have j20_value : Bounds (1 : ℝ) j20.value (1 : ℝ) := by
    simpa only [← hj20,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h51
  have j20_tangent : Bounds (-1/16 : ℝ) j20.tangent (-1/16 : ℝ) := by
    simpa only [← hj20,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h54
  let v55 : ℝ := -j20.value
  have h55 : Bounds (-1 : ℝ) v55 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg j20_value) (by norm_num) (by norm_num)
  let v56 : ℝ := j0.value+v55
  have h56 : Bounds (0 : ℝ) v56 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h55) (by norm_num) (by norm_num)
  let v57 : ℝ := -j20.tangent
  have h57 : Bounds (1/16 : ℝ) v57 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j20_tangent) (by norm_num) (by norm_num)
  let v58 : ℝ := j0.tangent+v57
  have h58 : Bounds (1/16 : ℝ) v58 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h57) (by norm_num) (by norm_num)
  obtain ⟨j21,hj21⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j20=z := ⟨_,rfl⟩
  have j21_value : Bounds (0 : ℝ) j21.value (0 : ℝ) := by
    simpa only [← hj21,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h56
  have j21_tangent : Bounds (1/16 : ℝ) j21.tangent (1/16 : ℝ) := by
    simpa only [← hj21,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h58
  let v59 : ℝ := j21.value*j0.value
  have h59 : Bounds (0 : ℝ) v59 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v60 : ℝ := j21.tangent*j0.value
  have h60 : Bounds (1/16 : ℝ) v60 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v61 : ℝ := j21.value*j0.tangent
  have h61 : Bounds (0 : ℝ) v61 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v62 : ℝ := v60+v61
  have h62 : Bounds (1/16 : ℝ) v62 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h60 h61) (by norm_num) (by norm_num)
  obtain ⟨j22,hj22⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j21 j0=z := ⟨_,rfl⟩
  have j22_value : Bounds (0 : ℝ) j22.value (0 : ℝ) := by
    simpa only [← hj22,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h59
  have j22_tangent : Bounds (1/16 : ℝ) j22.tangent (1/16 : ℝ) := by
    simpa only [← hj22,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h62
  let v63 : ℝ := j9.value*j11.value
  have h63 : Bounds (1/8 : ℝ) v63 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j9_value j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v64 : ℝ := j9.tangent*j11.value
  have h64 : Bounds (0 : ℝ) v64 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j9_tangent j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v65 : ℝ := j9.value*j11.tangent
  have h65 : Bounds (0 : ℝ) v65 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j11_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v66 : ℝ := v64+v65
  have h66 : Bounds (0 : ℝ) v66 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h64 h65) (by norm_num) (by norm_num)
  obtain ⟨j23,hj23⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j11=z := ⟨_,rfl⟩
  have j23_value : Bounds (1/8 : ℝ) j23.value (1/8 : ℝ) := by
    simpa only [← hj23,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h63
  have j23_tangent : Bounds (0 : ℝ) j23.tangent (0 : ℝ) := by
    simpa only [← hj23,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h66
  let v67 : ℝ := j18.value*j23.value
  have h67 : Bounds (1/16 : ℝ) v67 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j23_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v68 : ℝ := j18.tangent*j23.value
  have h68 : Bounds (-1/256 : ℝ) v68 (-1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j23_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v69 : ℝ := j18.value*j23.tangent
  have h69 : Bounds (0 : ℝ) v69 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j23_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v70 : ℝ := v68+v69
  have h70 : Bounds (-1/256 : ℝ) v70 (-1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add h68 h69) (by norm_num) (by norm_num)
  obtain ⟨j24,hj24⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j23=z := ⟨_,rfl⟩
  have j24_value : Bounds (1/16 : ℝ) j24.value (1/16 : ℝ) := by
    simpa only [← hj24,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h67
  have j24_tangent : Bounds (-1/256 : ℝ) j24.tangent (-1/256 : ℝ) := by
    simpa only [← hj24,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h70
  let v71 : ℝ := -j24.value
  have h71 : Bounds (-1/16 : ℝ) v71 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j24_value) (by norm_num) (by norm_num)
  let v72 : ℝ := j6.value+v71
  have h72 : Bounds (-1/16 : ℝ) v72 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h71) (by norm_num) (by norm_num)
  let v73 : ℝ := -j24.tangent
  have h73 : Bounds (1/256 : ℝ) v73 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.neg j24_tangent) (by norm_num) (by norm_num)
  let v74 : ℝ := j6.tangent+v73
  have h74 : Bounds (1/256 : ℝ) v74 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h73) (by norm_num) (by norm_num)
  obtain ⟨j25,hj25⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j24=z := ⟨_,rfl⟩
  have j25_value : Bounds (-1/16 : ℝ) j25.value (-1/16 : ℝ) := by
    simpa only [← hj25,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h72
  have j25_tangent : Bounds (1/256 : ℝ) j25.tangent (1/256 : ℝ) := by
    simpa only [← hj25,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h74
  let v75 : ℝ := j25.value*j1.value
  have h75 : Bounds (0 : ℝ) v75 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v76 : ℝ := j25.tangent*j1.value
  have h76 : Bounds (0 : ℝ) v76 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j25_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v77 : ℝ := j25.value*j1.tangent
  have h77 : Bounds (-1/16 : ℝ) v77 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v78 : ℝ := v76+v77
  have h78 : Bounds (-1/16 : ℝ) v78 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h76 h77) (by norm_num) (by norm_num)
  obtain ⟨j26,hj26⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j25 j1=z := ⟨_,rfl⟩
  have j26_value : Bounds (0 : ℝ) j26.value (0 : ℝ) := by
    simpa only [← hj26,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h75
  have j26_tangent : Bounds (-1/16 : ℝ) j26.tangent (-1/16 : ℝ) := by
    simpa only [← hj26,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h78
  let v79 : ℝ := j22.value+j26.value
  have h79 : Bounds (0 : ℝ) v79 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j22_value j26_value) (by norm_num) (by norm_num)
  let v80 : ℝ := j22.tangent+j26.tangent
  have h80 : Bounds (0 : ℝ) v80 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j22_tangent j26_tangent) (by norm_num) (by norm_num)
  obtain ⟨j27,hj27⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j22 j26=z := ⟨_,rfl⟩
  have j27_value : Bounds (0 : ℝ) j27.value (0 : ℝ) := by
    simpa only [← hj27,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h79
  have j27_tangent : Bounds (0 : ℝ) j27.tangent (0 : ℝ) := by
    simpa only [← hj27,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h80
  let v81 : ℝ := j18.value*j10.value
  have h81 : Bounds (1 : ℝ) v81 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j10_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v82 : ℝ := j18.tangent*j10.value
  have h82 : Bounds (-1/16 : ℝ) v82 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j10_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v83 : ℝ := j18.value*j10.tangent
  have h83 : Bounds (0 : ℝ) v83 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j10_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v84 : ℝ := v82+v83
  have h84 : Bounds (-1/16 : ℝ) v84 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h82 h83) (by norm_num) (by norm_num)
  obtain ⟨j28,hj28⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j10=z := ⟨_,rfl⟩
  have j28_value : Bounds (1 : ℝ) j28.value (1 : ℝ) := by
    simpa only [← hj28,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h81
  have j28_tangent : Bounds (-1/16 : ℝ) j28.tangent (-1/16 : ℝ) := by
    simpa only [← hj28,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h84
  let v85 : ℝ := -j28.value
  have h85 : Bounds (-1 : ℝ) v85 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg j28_value) (by norm_num) (by norm_num)
  let v86 : ℝ := j0.value+v85
  have h86 : Bounds (0 : ℝ) v86 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h85) (by norm_num) (by norm_num)
  let v87 : ℝ := -j28.tangent
  have h87 : Bounds (1/16 : ℝ) v87 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j28_tangent) (by norm_num) (by norm_num)
  let v88 : ℝ := j0.tangent+v87
  have h88 : Bounds (1/16 : ℝ) v88 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h87) (by norm_num) (by norm_num)
  obtain ⟨j29,hj29⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j28=z := ⟨_,rfl⟩
  have j29_value : Bounds (0 : ℝ) j29.value (0 : ℝ) := by
    simpa only [← hj29,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h86
  have j29_tangent : Bounds (1/16 : ℝ) j29.tangent (1/16 : ℝ) := by
    simpa only [← hj29,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h88
  let v89 : ℝ := j27.value*j29.value
  have h89 : Bounds (0 : ℝ) v89 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_value j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v90 : ℝ := j27.tangent*j29.value
  have h90 : Bounds (0 : ℝ) v90 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_tangent j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v91 : ℝ := j27.value*j29.tangent
  have h91 : Bounds (0 : ℝ) v91 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_value j29_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v92 : ℝ := v90+v91
  have h92 : Bounds (0 : ℝ) v92 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h90 h91) (by norm_num) (by norm_num)
  obtain ⟨j30,hj30⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j27 j29=z := ⟨_,rfl⟩
  have j30_value : Bounds (0 : ℝ) j30.value (0 : ℝ) := by
    simpa only [← hj30,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h89
  have j30_tangent : Bounds (0 : ℝ) j30.tangent (0 : ℝ) := by
    simpa only [← hj30,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h92
  let v93 : ℝ := j21.value*j1.value
  have h93 : Bounds (0 : ℝ) v93 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v94 : ℝ := j21.tangent*j1.value
  have h94 : Bounds (0 : ℝ) v94 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v95 : ℝ := j21.value*j1.tangent
  have h95 : Bounds (0 : ℝ) v95 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v96 : ℝ := v94+v95
  have h96 : Bounds (0 : ℝ) v96 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h94 h95) (by norm_num) (by norm_num)
  obtain ⟨j31,hj31⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j21 j1=z := ⟨_,rfl⟩
  have j31_value : Bounds (0 : ℝ) j31.value (0 : ℝ) := by
    simpa only [← hj31,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h93
  have j31_tangent : Bounds (0 : ℝ) j31.tangent (0 : ℝ) := by
    simpa only [← hj31,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h96
  let v97 : ℝ := j25.value*j2.value
  have h97 : Bounds (-1/16 : ℝ) v97 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v98 : ℝ := j25.tangent*j2.value
  have h98 : Bounds (1/256 : ℝ) v98 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j25_tangent j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v99 : ℝ := j25.value*j2.tangent
  have h99 : Bounds (0 : ℝ) v99 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j2_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v100 : ℝ := v98+v99
  have h100 : Bounds (1/256 : ℝ) v100 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add h98 h99) (by norm_num) (by norm_num)
  obtain ⟨j32,hj32⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j25 j2=z := ⟨_,rfl⟩
  have j32_value : Bounds (-1/16 : ℝ) j32.value (-1/16 : ℝ) := by
    simpa only [← hj32,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h97
  have j32_tangent : Bounds (1/256 : ℝ) j32.tangent (1/256 : ℝ) := by
    simpa only [← hj32,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h100
  let v101 : ℝ := j31.value+j32.value
  have h101 : Bounds (-1/16 : ℝ) v101 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j31_value j32_value) (by norm_num) (by norm_num)
  let v102 : ℝ := j31.tangent+j32.tangent
  have h102 : Bounds (1/256 : ℝ) v102 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j31_tangent j32_tangent) (by norm_num) (by norm_num)
  obtain ⟨j33,hj33⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j31 j32=z := ⟨_,rfl⟩
  have j33_value : Bounds (-1/16 : ℝ) j33.value (-1/16 : ℝ) := by
    simpa only [← hj33,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h101
  have j33_tangent : Bounds (1/256 : ℝ) j33.tangent (1/256 : ℝ) := by
    simpa only [← hj33,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h102
  let v103 : ℝ := j11.value*j9.value
  have h103 : Bounds (1/8 : ℝ) v103 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j11_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v104 : ℝ := j11.tangent*j9.value
  have h104 : Bounds (0 : ℝ) v104 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j11_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v105 : ℝ := j11.value*j9.tangent
  have h105 : Bounds (0 : ℝ) v105 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j11_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v106 : ℝ := v104+v105
  have h106 : Bounds (0 : ℝ) v106 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h104 h105) (by norm_num) (by norm_num)
  obtain ⟨j34,hj34⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j11 j9=z := ⟨_,rfl⟩
  have j34_value : Bounds (1/8 : ℝ) j34.value (1/8 : ℝ) := by
    simpa only [← hj34,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h103
  have j34_tangent : Bounds (0 : ℝ) j34.tangent (0 : ℝ) := by
    simpa only [← hj34,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h106
  let v107 : ℝ := j18.value*j34.value
  have h107 : Bounds (1/16 : ℝ) v107 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j34_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v108 : ℝ := j18.tangent*j34.value
  have h108 : Bounds (-1/256 : ℝ) v108 (-1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j34_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v109 : ℝ := j18.value*j34.tangent
  have h109 : Bounds (0 : ℝ) v109 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j34_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v110 : ℝ := v108+v109
  have h110 : Bounds (-1/256 : ℝ) v110 (-1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add h108 h109) (by norm_num) (by norm_num)
  obtain ⟨j35,hj35⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j34=z := ⟨_,rfl⟩
  have j35_value : Bounds (1/16 : ℝ) j35.value (1/16 : ℝ) := by
    simpa only [← hj35,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h107
  have j35_tangent : Bounds (-1/256 : ℝ) j35.tangent (-1/256 : ℝ) := by
    simpa only [← hj35,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h110
  let v111 : ℝ := -j35.value
  have h111 : Bounds (-1/16 : ℝ) v111 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j35_value) (by norm_num) (by norm_num)
  let v112 : ℝ := j6.value+v111
  have h112 : Bounds (-1/16 : ℝ) v112 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h111) (by norm_num) (by norm_num)
  let v113 : ℝ := -j35.tangent
  have h113 : Bounds (1/256 : ℝ) v113 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.neg j35_tangent) (by norm_num) (by norm_num)
  let v114 : ℝ := j6.tangent+v113
  have h114 : Bounds (1/256 : ℝ) v114 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h113) (by norm_num) (by norm_num)
  obtain ⟨j36,hj36⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j35=z := ⟨_,rfl⟩
  have j36_value : Bounds (-1/16 : ℝ) j36.value (-1/16 : ℝ) := by
    simpa only [← hj36,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h112
  have j36_tangent : Bounds (1/256 : ℝ) j36.tangent (1/256 : ℝ) := by
    simpa only [← hj36,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h114
  let v115 : ℝ := j33.value*j36.value
  have h115 : Bounds (1/256 : ℝ) v115 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j33_value j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v116 : ℝ := j33.tangent*j36.value
  have h116 : Bounds (-1/4096 : ℝ) v116 (-1/4096 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j33_tangent j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v117 : ℝ := j33.value*j36.tangent
  have h117 : Bounds (-1/4096 : ℝ) v117 (-1/4096 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j33_value j36_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v118 : ℝ := v116+v117
  have h118 : Bounds (-1/2048 : ℝ) v118 (-1/2048 : ℝ) := by
    exact enlarge (IntervalBounds.add h116 h117) (by norm_num) (by norm_num)
  obtain ⟨j37,hj37⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j33 j36=z := ⟨_,rfl⟩
  have j37_value : Bounds (1/256 : ℝ) j37.value (1/256 : ℝ) := by
    simpa only [← hj37,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h115
  have j37_tangent : Bounds (-1/2048 : ℝ) j37.tangent (-1/2048 : ℝ) := by
    simpa only [← hj37,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h118
  let v119 : ℝ := j30.value+j37.value
  have h119 : Bounds (1/256 : ℝ) v119 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j30_value j37_value) (by norm_num) (by norm_num)
  let v120 : ℝ := j30.tangent+j37.tangent
  have h120 : Bounds (-1/2048 : ℝ) v120 (-1/2048 : ℝ) := by
    exact enlarge (IntervalBounds.add j30_tangent j37_tangent) (by norm_num) (by norm_num)
  obtain ⟨j38,hj38⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j30 j37=z := ⟨_,rfl⟩
  have j38_value : Bounds (1/256 : ℝ) j38.value (1/256 : ℝ) := by
    simpa only [← hj38,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h119
  have j38_tangent : Bounds (-1/2048 : ℝ) j38.tangent (-1/2048 : ℝ) := by
    simpa only [← hj38,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h120
  let v121 : ℝ := j9.value*j9.value
  have h121 : Bounds (1 : ℝ) v121 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j9_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v122 : ℝ := j9.tangent*j9.value
  have h122 : Bounds (0 : ℝ) v122 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j9_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v123 : ℝ := j9.value*j9.tangent
  have h123 : Bounds (0 : ℝ) v123 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v124 : ℝ := v122+v123
  have h124 : Bounds (0 : ℝ) v124 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h122 h123) (by norm_num) (by norm_num)
  obtain ⟨j39,hj39⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j9=z := ⟨_,rfl⟩
  have j39_value : Bounds (1 : ℝ) j39.value (1 : ℝ) := by
    simpa only [← hj39,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h121
  have j39_tangent : Bounds (0 : ℝ) j39.tangent (0 : ℝ) := by
    simpa only [← hj39,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h124
  let v125 : ℝ := j18.value*j39.value
  have h125 : Bounds (1/2 : ℝ) v125 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j39_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v126 : ℝ := j18.tangent*j39.value
  have h126 : Bounds (-1/32 : ℝ) v126 (-1/32 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j39_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v127 : ℝ := j18.value*j39.tangent
  have h127 : Bounds (0 : ℝ) v127 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j39_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v128 : ℝ := v126+v127
  have h128 : Bounds (-1/32 : ℝ) v128 (-1/32 : ℝ) := by
    exact enlarge (IntervalBounds.add h126 h127) (by norm_num) (by norm_num)
  obtain ⟨j40,hj40⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j39=z := ⟨_,rfl⟩
  have j40_value : Bounds (1/2 : ℝ) j40.value (1/2 : ℝ) := by
    simpa only [← hj40,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h125
  have j40_tangent : Bounds (-1/32 : ℝ) j40.tangent (-1/32 : ℝ) := by
    simpa only [← hj40,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h128
  let v129 : ℝ := j38.value+j40.value
  have h129 : Bounds (129/256 : ℝ) v129 (129/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j38_value j40_value) (by norm_num) (by norm_num)
  let v130 : ℝ := j38.tangent+j40.tangent
  have h130 : Bounds (-65/2048 : ℝ) v130 (-65/2048 : ℝ) := by
    exact enlarge (IntervalBounds.add j38_tangent j40_tangent) (by norm_num) (by norm_num)
  obtain ⟨j41,hj41⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j38 j40=z := ⟨_,rfl⟩
  have j41_value : Bounds (129/256 : ℝ) j41.value (129/256 : ℝ) := by
    simpa only [← hj41,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h129
  have j41_tangent : Bounds (-65/2048 : ℝ) j41.tangent (-65/2048 : ℝ) := by
    simpa only [← hj41,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h130
  let v131 : ℝ := j3.value*j15.value
  have h131 : Bounds (0 : ℝ) v131 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j3_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v132 : ℝ := j3.tangent*j15.value
  have h132 : Bounds (0 : ℝ) v132 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j3_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v133 : ℝ := j3.value*j15.tangent
  have h133 : Bounds (2 : ℝ) v133 (2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j3_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v134 : ℝ := v132+v133
  have h134 : Bounds (2 : ℝ) v134 (2 : ℝ) := by
    exact enlarge (IntervalBounds.add h132 h133) (by norm_num) (by norm_num)
  obtain ⟨j42,hj42⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j3 j15=z := ⟨_,rfl⟩
  have j42_value : Bounds (0 : ℝ) j42.value (0 : ℝ) := by
    simpa only [← hj42,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h131
  have j42_tangent : Bounds (2 : ℝ) j42.tangent (2 : ℝ) := by
    simpa only [← hj42,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h134
  let v135 : ℝ := j18.value*j42.value
  have h135 : Bounds (0 : ℝ) v135 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j42_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v136 : ℝ := j18.tangent*j42.value
  have h136 : Bounds (0 : ℝ) v136 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j42_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v137 : ℝ := j18.value*j42.tangent
  have h137 : Bounds (1 : ℝ) v137 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j42_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v138 : ℝ := v136+v137
  have h138 : Bounds (1 : ℝ) v138 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h136 h137) (by norm_num) (by norm_num)
  obtain ⟨j43,hj43⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j42=z := ⟨_,rfl⟩
  have j43_value : Bounds (0 : ℝ) j43.value (0 : ℝ) := by
    simpa only [← hj43,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h135
  have j43_tangent : Bounds (1 : ℝ) j43.tangent (1 : ℝ) := by
    simpa only [← hj43,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h138
  let v139 : ℝ := -j43.value
  have h139 : Bounds (0 : ℝ) v139 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j43_value) (by norm_num) (by norm_num)
  let v140 : ℝ := j6.value+v139
  have h140 : Bounds (0 : ℝ) v140 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h139) (by norm_num) (by norm_num)
  let v141 : ℝ := -j43.tangent
  have h141 : Bounds (-1 : ℝ) v141 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg j43_tangent) (by norm_num) (by norm_num)
  let v142 : ℝ := j6.tangent+v141
  have h142 : Bounds (-1 : ℝ) v142 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h141) (by norm_num) (by norm_num)
  obtain ⟨j44,hj44⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j43=z := ⟨_,rfl⟩
  have j44_value : Bounds (0 : ℝ) j44.value (0 : ℝ) := by
    simpa only [← hj44,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h140
  have j44_tangent : Bounds (-1 : ℝ) j44.tangent (-1 : ℝ) := by
    simpa only [← hj44,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h142
  let v143 : ℝ := j27.value*j44.value
  have h143 : Bounds (0 : ℝ) v143 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_value j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v144 : ℝ := j27.tangent*j44.value
  have h144 : Bounds (0 : ℝ) v144 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_tangent j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v145 : ℝ := j27.value*j44.tangent
  have h145 : Bounds (0 : ℝ) v145 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j27_value j44_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v146 : ℝ := v144+v145
  have h146 : Bounds (0 : ℝ) v146 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h144 h145) (by norm_num) (by norm_num)
  obtain ⟨j45,hj45⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j27 j44=z := ⟨_,rfl⟩
  have j45_value : Bounds (0 : ℝ) j45.value (0 : ℝ) := by
    simpa only [← hj45,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h143
  have j45_tangent : Bounds (0 : ℝ) j45.tangent (0 : ℝ) := by
    simpa only [← hj45,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h146
  let v147 : ℝ := j18.value*j16.value
  have h147 : Bounds (0 : ℝ) v147 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j16_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v148 : ℝ := j18.tangent*j16.value
  have h148 : Bounds (0 : ℝ) v148 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j16_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v149 : ℝ := j18.value*j16.tangent
  have h149 : Bounds (1/16 : ℝ) v149 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j16_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v150 : ℝ := v148+v149
  have h150 : Bounds (1/16 : ℝ) v150 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h148 h149) (by norm_num) (by norm_num)
  obtain ⟨j46,hj46⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j16=z := ⟨_,rfl⟩
  have j46_value : Bounds (0 : ℝ) j46.value (0 : ℝ) := by
    simpa only [← hj46,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h147
  have j46_tangent : Bounds (1/16 : ℝ) j46.tangent (1/16 : ℝ) := by
    simpa only [← hj46,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h150
  let v151 : ℝ := -j46.value
  have h151 : Bounds (0 : ℝ) v151 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j46_value) (by norm_num) (by norm_num)
  let v152 : ℝ := j0.value+v151
  have h152 : Bounds (1 : ℝ) v152 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h151) (by norm_num) (by norm_num)
  let v153 : ℝ := -j46.tangent
  have h153 : Bounds (-1/16 : ℝ) v153 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j46_tangent) (by norm_num) (by norm_num)
  let v154 : ℝ := j0.tangent+v153
  have h154 : Bounds (-1/16 : ℝ) v154 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h153) (by norm_num) (by norm_num)
  obtain ⟨j47,hj47⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j46=z := ⟨_,rfl⟩
  have j47_value : Bounds (1 : ℝ) j47.value (1 : ℝ) := by
    simpa only [← hj47,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h152
  have j47_tangent : Bounds (-1/16 : ℝ) j47.tangent (-1/16 : ℝ) := by
    simpa only [← hj47,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h154
  let v155 : ℝ := j33.value*j47.value
  have h155 : Bounds (-1/16 : ℝ) v155 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j33_value j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v156 : ℝ := j33.tangent*j47.value
  have h156 : Bounds (1/256 : ℝ) v156 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j33_tangent j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v157 : ℝ := j33.value*j47.tangent
  have h157 : Bounds (1/256 : ℝ) v157 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j33_value j47_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v158 : ℝ := v156+v157
  have h158 : Bounds (1/128 : ℝ) v158 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.add h156 h157) (by norm_num) (by norm_num)
  obtain ⟨j48,hj48⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j33 j47=z := ⟨_,rfl⟩
  have j48_value : Bounds (-1/16 : ℝ) j48.value (-1/16 : ℝ) := by
    simpa only [← hj48,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h155
  have j48_tangent : Bounds (1/128 : ℝ) j48.tangent (1/128 : ℝ) := by
    simpa only [← hj48,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h158
  let v159 : ℝ := j45.value+j48.value
  have h159 : Bounds (-1/16 : ℝ) v159 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j45_value j48_value) (by norm_num) (by norm_num)
  let v160 : ℝ := j45.tangent+j48.tangent
  have h160 : Bounds (1/128 : ℝ) v160 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.add j45_tangent j48_tangent) (by norm_num) (by norm_num)
  obtain ⟨j49,hj49⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j45 j48=z := ⟨_,rfl⟩
  have j49_value : Bounds (-1/16 : ℝ) j49.value (-1/16 : ℝ) := by
    simpa only [← hj49,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h159
  have j49_tangent : Bounds (1/128 : ℝ) j49.tangent (1/128 : ℝ) := by
    simpa only [← hj49,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h160
  let v161 : ℝ := j9.value*j15.value
  have h161 : Bounds (0 : ℝ) v161 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v162 : ℝ := j9.tangent*j15.value
  have h162 : Bounds (0 : ℝ) v162 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j9_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v163 : ℝ := j9.value*j15.tangent
  have h163 : Bounds (1 : ℝ) v163 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j9_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v164 : ℝ := v162+v163
  have h164 : Bounds (1 : ℝ) v164 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h162 h163) (by norm_num) (by norm_num)
  obtain ⟨j50,hj50⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j15=z := ⟨_,rfl⟩
  have j50_value : Bounds (0 : ℝ) j50.value (0 : ℝ) := by
    simpa only [← hj50,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h161
  have j50_tangent : Bounds (1 : ℝ) j50.tangent (1 : ℝ) := by
    simpa only [← hj50,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h164
  let v165 : ℝ := j18.value*j50.value
  have h165 : Bounds (0 : ℝ) v165 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j50_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v166 : ℝ := j18.tangent*j50.value
  have h166 : Bounds (0 : ℝ) v166 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j50_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v167 : ℝ := j18.value*j50.tangent
  have h167 : Bounds (1/2 : ℝ) v167 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j50_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v168 : ℝ := v166+v167
  have h168 : Bounds (1/2 : ℝ) v168 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.add h166 h167) (by norm_num) (by norm_num)
  obtain ⟨j51,hj51⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j50=z := ⟨_,rfl⟩
  have j51_value : Bounds (0 : ℝ) j51.value (0 : ℝ) := by
    simpa only [← hj51,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h165
  have j51_tangent : Bounds (1/2 : ℝ) j51.tangent (1/2 : ℝ) := by
    simpa only [← hj51,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h168
  let v169 : ℝ := j49.value+j51.value
  have h169 : Bounds (-1/16 : ℝ) v169 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j49_value j51_value) (by norm_num) (by norm_num)
  let v170 : ℝ := j49.tangent+j51.tangent
  have h170 : Bounds (65/128 : ℝ) v170 (65/128 : ℝ) := by
    exact enlarge (IntervalBounds.add j49_tangent j51_tangent) (by norm_num) (by norm_num)
  obtain ⟨j52,hj52⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j49 j51=z := ⟨_,rfl⟩
  have j52_value : Bounds (-1/16 : ℝ) j52.value (-1/16 : ℝ) := by
    simpa only [← hj52,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h169
  have j52_tangent : Bounds (65/128 : ℝ) j52.tangent (65/128 : ℝ) := by
    simpa only [← hj52,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h170
  let v171 : ℝ := j15.value*j3.value
  have h171 : Bounds (0 : ℝ) v171 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_value j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v172 : ℝ := j15.tangent*j3.value
  have h172 : Bounds (2 : ℝ) v172 (2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j15_tangent j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v173 : ℝ := j15.value*j3.tangent
  have h173 : Bounds (0 : ℝ) v173 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j3_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v174 : ℝ := v172+v173
  have h174 : Bounds (2 : ℝ) v174 (2 : ℝ) := by
    exact enlarge (IntervalBounds.add h172 h173) (by norm_num) (by norm_num)
  obtain ⟨j53,hj53⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j3=z := ⟨_,rfl⟩
  have j53_value : Bounds (0 : ℝ) j53.value (0 : ℝ) := by
    simpa only [← hj53,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h171
  have j53_tangent : Bounds (2 : ℝ) j53.tangent (2 : ℝ) := by
    simpa only [← hj53,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h174
  let v175 : ℝ := j18.value*j53.value
  have h175 : Bounds (0 : ℝ) v175 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j53_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v176 : ℝ := j18.tangent*j53.value
  have h176 : Bounds (0 : ℝ) v176 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j53_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v177 : ℝ := j18.value*j53.tangent
  have h177 : Bounds (1 : ℝ) v177 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j53_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v178 : ℝ := v176+v177
  have h178 : Bounds (1 : ℝ) v178 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h176 h177) (by norm_num) (by norm_num)
  obtain ⟨j54,hj54⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j53=z := ⟨_,rfl⟩
  have j54_value : Bounds (0 : ℝ) j54.value (0 : ℝ) := by
    simpa only [← hj54,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h175
  have j54_tangent : Bounds (1 : ℝ) j54.tangent (1 : ℝ) := by
    simpa only [← hj54,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h178
  let v179 : ℝ := -j54.value
  have h179 : Bounds (0 : ℝ) v179 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j54_value) (by norm_num) (by norm_num)
  let v180 : ℝ := j6.value+v179
  have h180 : Bounds (0 : ℝ) v180 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h179) (by norm_num) (by norm_num)
  let v181 : ℝ := -j54.tangent
  have h181 : Bounds (-1 : ℝ) v181 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg j54_tangent) (by norm_num) (by norm_num)
  let v182 : ℝ := j6.tangent+v181
  have h182 : Bounds (-1 : ℝ) v182 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h181) (by norm_num) (by norm_num)
  obtain ⟨j55,hj55⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j54=z := ⟨_,rfl⟩
  have j55_value : Bounds (0 : ℝ) j55.value (0 : ℝ) := by
    simpa only [← hj55,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h180
  have j55_tangent : Bounds (-1 : ℝ) j55.tangent (-1 : ℝ) := by
    simpa only [← hj55,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h182
  let v183 : ℝ := j55.value*j0.value
  have h183 : Bounds (0 : ℝ) v183 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v184 : ℝ := j55.tangent*j0.value
  have h184 : Bounds (-1 : ℝ) v184 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j55_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v185 : ℝ := j55.value*j0.tangent
  have h185 : Bounds (0 : ℝ) v185 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v186 : ℝ := v184+v185
  have h186 : Bounds (-1 : ℝ) v186 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.add h184 h185) (by norm_num) (by norm_num)
  obtain ⟨j56,hj56⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j55 j0=z := ⟨_,rfl⟩
  have j56_value : Bounds (0 : ℝ) j56.value (0 : ℝ) := by
    simpa only [← hj56,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h183
  have j56_tangent : Bounds (-1 : ℝ) j56.tangent (-1 : ℝ) := by
    simpa only [← hj56,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h186
  let v187 : ℝ := j15.value*j11.value
  have h187 : Bounds (0 : ℝ) v187 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_value j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v188 : ℝ := j15.tangent*j11.value
  have h188 : Bounds (1/8 : ℝ) v188 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j15_tangent j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v189 : ℝ := j15.value*j11.tangent
  have h189 : Bounds (0 : ℝ) v189 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j11_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v190 : ℝ := v188+v189
  have h190 : Bounds (1/8 : ℝ) v190 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add h188 h189) (by norm_num) (by norm_num)
  obtain ⟨j57,hj57⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j11=z := ⟨_,rfl⟩
  have j57_value : Bounds (0 : ℝ) j57.value (0 : ℝ) := by
    simpa only [← hj57,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h187
  have j57_tangent : Bounds (1/8 : ℝ) j57.tangent (1/8 : ℝ) := by
    simpa only [← hj57,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h190
  let v191 : ℝ := j18.value*j57.value
  have h191 : Bounds (0 : ℝ) v191 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j57_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v192 : ℝ := j18.tangent*j57.value
  have h192 : Bounds (0 : ℝ) v192 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j57_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v193 : ℝ := j18.value*j57.tangent
  have h193 : Bounds (1/16 : ℝ) v193 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j57_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v194 : ℝ := v192+v193
  have h194 : Bounds (1/16 : ℝ) v194 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h192 h193) (by norm_num) (by norm_num)
  obtain ⟨j58,hj58⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j57=z := ⟨_,rfl⟩
  have j58_value : Bounds (0 : ℝ) j58.value (0 : ℝ) := by
    simpa only [← hj58,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h191
  have j58_tangent : Bounds (1/16 : ℝ) j58.tangent (1/16 : ℝ) := by
    simpa only [← hj58,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h194
  let v195 : ℝ := -j58.value
  have h195 : Bounds (0 : ℝ) v195 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j58_value) (by norm_num) (by norm_num)
  let v196 : ℝ := j0.value+v195
  have h196 : Bounds (1 : ℝ) v196 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h195) (by norm_num) (by norm_num)
  let v197 : ℝ := -j58.tangent
  have h197 : Bounds (-1/16 : ℝ) v197 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j58_tangent) (by norm_num) (by norm_num)
  let v198 : ℝ := j0.tangent+v197
  have h198 : Bounds (-1/16 : ℝ) v198 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h197) (by norm_num) (by norm_num)
  obtain ⟨j59,hj59⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j58=z := ⟨_,rfl⟩
  have j59_value : Bounds (1 : ℝ) j59.value (1 : ℝ) := by
    simpa only [← hj59,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h196
  have j59_tangent : Bounds (-1/16 : ℝ) j59.tangent (-1/16 : ℝ) := by
    simpa only [← hj59,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h198
  let v199 : ℝ := j59.value*j1.value
  have h199 : Bounds (0 : ℝ) v199 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v200 : ℝ := j59.tangent*j1.value
  have h200 : Bounds (0 : ℝ) v200 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j59_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v201 : ℝ := j59.value*j1.tangent
  have h201 : Bounds (1 : ℝ) v201 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v202 : ℝ := v200+v201
  have h202 : Bounds (1 : ℝ) v202 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h200 h201) (by norm_num) (by norm_num)
  obtain ⟨j60,hj60⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j59 j1=z := ⟨_,rfl⟩
  have j60_value : Bounds (0 : ℝ) j60.value (0 : ℝ) := by
    simpa only [← hj60,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h199
  have j60_tangent : Bounds (1 : ℝ) j60.tangent (1 : ℝ) := by
    simpa only [← hj60,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h202
  let v203 : ℝ := j56.value+j60.value
  have h203 : Bounds (0 : ℝ) v203 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j56_value j60_value) (by norm_num) (by norm_num)
  let v204 : ℝ := j56.tangent+j60.tangent
  have h204 : Bounds (0 : ℝ) v204 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j56_tangent j60_tangent) (by norm_num) (by norm_num)
  obtain ⟨j61,hj61⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j56 j60=z := ⟨_,rfl⟩
  have j61_value : Bounds (0 : ℝ) j61.value (0 : ℝ) := by
    simpa only [← hj61,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h203
  have j61_tangent : Bounds (0 : ℝ) j61.tangent (0 : ℝ) := by
    simpa only [← hj61,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h204
  let v205 : ℝ := j61.value*j29.value
  have h205 : Bounds (0 : ℝ) v205 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_value j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v206 : ℝ := j61.tangent*j29.value
  have h206 : Bounds (0 : ℝ) v206 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_tangent j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v207 : ℝ := j61.value*j29.tangent
  have h207 : Bounds (0 : ℝ) v207 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_value j29_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v208 : ℝ := v206+v207
  have h208 : Bounds (0 : ℝ) v208 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h206 h207) (by norm_num) (by norm_num)
  obtain ⟨j62,hj62⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j61 j29=z := ⟨_,rfl⟩
  have j62_value : Bounds (0 : ℝ) j62.value (0 : ℝ) := by
    simpa only [← hj62,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h205
  have j62_tangent : Bounds (0 : ℝ) j62.tangent (0 : ℝ) := by
    simpa only [← hj62,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h208
  let v209 : ℝ := j55.value*j1.value
  have h209 : Bounds (0 : ℝ) v209 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v210 : ℝ := j55.tangent*j1.value
  have h210 : Bounds (0 : ℝ) v210 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j55_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v211 : ℝ := j55.value*j1.tangent
  have h211 : Bounds (0 : ℝ) v211 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v212 : ℝ := v210+v211
  have h212 : Bounds (0 : ℝ) v212 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h210 h211) (by norm_num) (by norm_num)
  obtain ⟨j63,hj63⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j55 j1=z := ⟨_,rfl⟩
  have j63_value : Bounds (0 : ℝ) j63.value (0 : ℝ) := by
    simpa only [← hj63,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h209
  have j63_tangent : Bounds (0 : ℝ) j63.tangent (0 : ℝ) := by
    simpa only [← hj63,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h212
  let v213 : ℝ := j59.value*j2.value
  have h213 : Bounds (1 : ℝ) v213 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v214 : ℝ := j59.tangent*j2.value
  have h214 : Bounds (-1/16 : ℝ) v214 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j59_tangent j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v215 : ℝ := j59.value*j2.tangent
  have h215 : Bounds (0 : ℝ) v215 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j2_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v216 : ℝ := v214+v215
  have h216 : Bounds (-1/16 : ℝ) v216 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h214 h215) (by norm_num) (by norm_num)
  obtain ⟨j64,hj64⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j59 j2=z := ⟨_,rfl⟩
  have j64_value : Bounds (1 : ℝ) j64.value (1 : ℝ) := by
    simpa only [← hj64,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h213
  have j64_tangent : Bounds (-1/16 : ℝ) j64.tangent (-1/16 : ℝ) := by
    simpa only [← hj64,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h216
  let v217 : ℝ := j63.value+j64.value
  have h217 : Bounds (1 : ℝ) v217 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j63_value j64_value) (by norm_num) (by norm_num)
  let v218 : ℝ := j63.tangent+j64.tangent
  have h218 : Bounds (-1/16 : ℝ) v218 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j63_tangent j64_tangent) (by norm_num) (by norm_num)
  obtain ⟨j65,hj65⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j63 j64=z := ⟨_,rfl⟩
  have j65_value : Bounds (1 : ℝ) j65.value (1 : ℝ) := by
    simpa only [← hj65,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h217
  have j65_tangent : Bounds (-1/16 : ℝ) j65.tangent (-1/16 : ℝ) := by
    simpa only [← hj65,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h218
  let v219 : ℝ := j65.value*j36.value
  have h219 : Bounds (-1/16 : ℝ) v219 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j65_value j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v220 : ℝ := j65.tangent*j36.value
  have h220 : Bounds (1/256 : ℝ) v220 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j65_tangent j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v221 : ℝ := j65.value*j36.tangent
  have h221 : Bounds (1/256 : ℝ) v221 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j65_value j36_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v222 : ℝ := v220+v221
  have h222 : Bounds (1/128 : ℝ) v222 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.add h220 h221) (by norm_num) (by norm_num)
  obtain ⟨j66,hj66⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j65 j36=z := ⟨_,rfl⟩
  have j66_value : Bounds (-1/16 : ℝ) j66.value (-1/16 : ℝ) := by
    simpa only [← hj66,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h219
  have j66_tangent : Bounds (1/128 : ℝ) j66.tangent (1/128 : ℝ) := by
    simpa only [← hj66,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h222
  let v223 : ℝ := j62.value+j66.value
  have h223 : Bounds (-1/16 : ℝ) v223 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j62_value j66_value) (by norm_num) (by norm_num)
  let v224 : ℝ := j62.tangent+j66.tangent
  have h224 : Bounds (1/128 : ℝ) v224 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.add j62_tangent j66_tangent) (by norm_num) (by norm_num)
  obtain ⟨j67,hj67⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j62 j66=z := ⟨_,rfl⟩
  have j67_value : Bounds (-1/16 : ℝ) j67.value (-1/16 : ℝ) := by
    simpa only [← hj67,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h223
  have j67_tangent : Bounds (1/128 : ℝ) j67.tangent (1/128 : ℝ) := by
    simpa only [← hj67,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h224
  let v225 : ℝ := j15.value*j9.value
  have h225 : Bounds (0 : ℝ) v225 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v226 : ℝ := j15.tangent*j9.value
  have h226 : Bounds (1 : ℝ) v226 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j15_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v227 : ℝ := j15.value*j9.tangent
  have h227 : Bounds (0 : ℝ) v227 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v228 : ℝ := v226+v227
  have h228 : Bounds (1 : ℝ) v228 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h226 h227) (by norm_num) (by norm_num)
  obtain ⟨j68,hj68⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j9=z := ⟨_,rfl⟩
  have j68_value : Bounds (0 : ℝ) j68.value (0 : ℝ) := by
    simpa only [← hj68,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h225
  have j68_tangent : Bounds (1 : ℝ) j68.tangent (1 : ℝ) := by
    simpa only [← hj68,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h228
  let v229 : ℝ := j18.value*j68.value
  have h229 : Bounds (0 : ℝ) v229 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j68_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v230 : ℝ := j18.tangent*j68.value
  have h230 : Bounds (0 : ℝ) v230 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j68_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v231 : ℝ := j18.value*j68.tangent
  have h231 : Bounds (1/2 : ℝ) v231 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j68_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v232 : ℝ := v230+v231
  have h232 : Bounds (1/2 : ℝ) v232 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.add h230 h231) (by norm_num) (by norm_num)
  obtain ⟨j69,hj69⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j68=z := ⟨_,rfl⟩
  have j69_value : Bounds (0 : ℝ) j69.value (0 : ℝ) := by
    simpa only [← hj69,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h229
  have j69_tangent : Bounds (1/2 : ℝ) j69.tangent (1/2 : ℝ) := by
    simpa only [← hj69,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h232
  let v233 : ℝ := j67.value+j69.value
  have h233 : Bounds (-1/16 : ℝ) v233 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j67_value j69_value) (by norm_num) (by norm_num)
  let v234 : ℝ := j67.tangent+j69.tangent
  have h234 : Bounds (65/128 : ℝ) v234 (65/128 : ℝ) := by
    exact enlarge (IntervalBounds.add j67_tangent j69_tangent) (by norm_num) (by norm_num)
  obtain ⟨j70,hj70⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j67 j69=z := ⟨_,rfl⟩
  have j70_value : Bounds (-1/16 : ℝ) j70.value (-1/16 : ℝ) := by
    simpa only [← hj70,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h233
  have j70_tangent : Bounds (65/128 : ℝ) j70.tangent (65/128 : ℝ) := by
    simpa only [← hj70,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h234
  let v235 : ℝ := j61.value*j44.value
  have h235 : Bounds (0 : ℝ) v235 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_value j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v236 : ℝ := j61.tangent*j44.value
  have h236 : Bounds (0 : ℝ) v236 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_tangent j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v237 : ℝ := j61.value*j44.tangent
  have h237 : Bounds (0 : ℝ) v237 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j61_value j44_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v238 : ℝ := v236+v237
  have h238 : Bounds (0 : ℝ) v238 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h236 h237) (by norm_num) (by norm_num)
  obtain ⟨j71,hj71⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j61 j44=z := ⟨_,rfl⟩
  have j71_value : Bounds (0 : ℝ) j71.value (0 : ℝ) := by
    simpa only [← hj71,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h235
  have j71_tangent : Bounds (0 : ℝ) j71.tangent (0 : ℝ) := by
    simpa only [← hj71,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h238
  let v239 : ℝ := j65.value*j47.value
  have h239 : Bounds (1 : ℝ) v239 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j65_value j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v240 : ℝ := j65.tangent*j47.value
  have h240 : Bounds (-1/16 : ℝ) v240 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j65_tangent j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v241 : ℝ := j65.value*j47.tangent
  have h241 : Bounds (-1/16 : ℝ) v241 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j65_value j47_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v242 : ℝ := v240+v241
  have h242 : Bounds (-1/8 : ℝ) v242 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add h240 h241) (by norm_num) (by norm_num)
  obtain ⟨j72,hj72⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j65 j47=z := ⟨_,rfl⟩
  have j72_value : Bounds (1 : ℝ) j72.value (1 : ℝ) := by
    simpa only [← hj72,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h239
  have j72_tangent : Bounds (-1/8 : ℝ) j72.tangent (-1/8 : ℝ) := by
    simpa only [← hj72,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h242
  let v243 : ℝ := j71.value+j72.value
  have h243 : Bounds (1 : ℝ) v243 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j71_value j72_value) (by norm_num) (by norm_num)
  let v244 : ℝ := j71.tangent+j72.tangent
  have h244 : Bounds (-1/8 : ℝ) v244 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add j71_tangent j72_tangent) (by norm_num) (by norm_num)
  obtain ⟨j73,hj73⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j71 j72=z := ⟨_,rfl⟩
  have j73_value : Bounds (1 : ℝ) j73.value (1 : ℝ) := by
    simpa only [← hj73,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h243
  have j73_tangent : Bounds (-1/8 : ℝ) j73.tangent (-1/8 : ℝ) := by
    simpa only [← hj73,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h244
  let v245 : ℝ := j15.value*j15.value
  have h245 : Bounds (0 : ℝ) v245 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v246 : ℝ := j15.tangent*j15.value
  have h246 : Bounds (0 : ℝ) v246 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j15_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v247 : ℝ := j15.value*j15.tangent
  have h247 : Bounds (0 : ℝ) v247 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v248 : ℝ := v246+v247
  have h248 : Bounds (0 : ℝ) v248 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h246 h247) (by norm_num) (by norm_num)
  obtain ⟨j74,hj74⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j15=z := ⟨_,rfl⟩
  have j74_value : Bounds (0 : ℝ) j74.value (0 : ℝ) := by
    simpa only [← hj74,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h245
  have j74_tangent : Bounds (0 : ℝ) j74.tangent (0 : ℝ) := by
    simpa only [← hj74,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h248
  let v249 : ℝ := j18.value*j74.value
  have h249 : Bounds (0 : ℝ) v249 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j74_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v250 : ℝ := j18.tangent*j74.value
  have h250 : Bounds (0 : ℝ) v250 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j18_tangent j74_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v251 : ℝ := j18.value*j74.tangent
  have h251 : Bounds (0 : ℝ) v251 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j74_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v252 : ℝ := v250+v251
  have h252 : Bounds (0 : ℝ) v252 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h250 h251) (by norm_num) (by norm_num)
  obtain ⟨j75,hj75⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j74=z := ⟨_,rfl⟩
  have j75_value : Bounds (0 : ℝ) j75.value (0 : ℝ) := by
    simpa only [← hj75,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h249
  have j75_tangent : Bounds (0 : ℝ) j75.tangent (0 : ℝ) := by
    simpa only [← hj75,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h252
  let v253 : ℝ := j73.value+j75.value
  have h253 : Bounds (1 : ℝ) v253 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j73_value j75_value) (by norm_num) (by norm_num)
  let v254 : ℝ := j73.tangent+j75.tangent
  have h254 : Bounds (-1/8 : ℝ) v254 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add j73_tangent j75_tangent) (by norm_num) (by norm_num)
  obtain ⟨j76,hj76⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j73 j75=z := ⟨_,rfl⟩
  have j76_value : Bounds (1 : ℝ) j76.value (1 : ℝ) := by
    simpa only [← hj76,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h253
  have j76_tangent : Bounds (-1/8 : ℝ) j76.tangent (-1/8 : ℝ) := by
    simpa only [← hj76,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h254
  have hm01 : jetIter c d 0 1=!![j41,j52;j70,j76] := by
    rw [jetIter,hm00]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj5,← hj6,← hj7,← hj8,← hj9,← hj10,← hj11,← hj12,← hj13,← hj14,← hj15,← hj16,← hj17,← hj18,← hj19,← hj20,← hj21,← hj22,← hj23,← hj24,← hj25,← hj26,← hj27,← hj28,← hj29,← hj30,← hj31,← hj32,← hj33,← hj34,← hj35,← hj36,← hj37,← hj38,← hj39,← hj40,← hj41,← hj42,← hj43,← hj44,← hj45,← hj46,← hj47,← hj48,← hj49,← hj50,← hj51,← hj52,← hj53,← hj54,← hj55,← hj56,← hj57,← hj58,← hj59,← hj60,← hj61,← hj62,← hj63,← hj64,← hj65,← hj66,← hj67,← hj68,← hj69,← hj70,← hj71,← hj72,← hj73,← hj74,← hj75,← hj76]
    all_goals rfl
  let v255 : ℝ := -(-1 : ℝ)
  have h255 : Bounds (1 : ℝ) v255 (1 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (-1 : ℝ))) (by norm_num) (by norm_num)
  let v256 : ℝ := c+v255
  have h256 : Bounds (131848142762711/100000000000000 : ℝ) v256 (16481017845339/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hc h255) (by norm_num) (by norm_num)
  obtain ⟨j77,hj77⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (c+(-(-1 : ℝ)))=z := ⟨_,rfl⟩
  have j77_value : Bounds (131848142762711/100000000000000 : ℝ) j77.value (16481017845339/12500000000000 : ℝ) := by
    simpa only [← hj77,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h256
  have j77_tangent : Bounds (0 : ℝ) j77.tangent (0 : ℝ) := by
    simpa only [← hj77,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j78,hj78⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/4 : ℝ)=z := ⟨_,rfl⟩
  have j78_value : Bounds (-1/4 : ℝ) j78.value (-1/4 : ℝ) := by
    simpa only [← hj78,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/4 : ℝ))
  have j78_tangent : Bounds (0 : ℝ) j78.tangent (0 : ℝ) := by
    simpa only [← hj78,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v257 : ℝ := j41.value*j4.value
  have h257 : Bounds (-129/256 : ℝ) v257 (-129/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j41_value j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v258 : ℝ := j41.tangent*j4.value
  have h258 : Bounds (65/2048 : ℝ) v258 (65/2048 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j41_tangent j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v259 : ℝ := j41.value*j4.tangent
  have h259 : Bounds (0 : ℝ) v259 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j41_value j4_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v260 : ℝ := v258+v259
  have h260 : Bounds (65/2048 : ℝ) v260 (65/2048 : ℝ) := by
    exact enlarge (IntervalBounds.add h258 h259) (by norm_num) (by norm_num)
  obtain ⟨j79,hj79⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j41 j4=z := ⟨_,rfl⟩
  have j79_value : Bounds (-129/256 : ℝ) j79.value (-129/256 : ℝ) := by
    simpa only [← hj79,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h257
  have j79_tangent : Bounds (65/2048 : ℝ) j79.tangent (65/2048 : ℝ) := by
    simpa only [← hj79,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h260
  obtain ⟨j80,hj80⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/8 : ℝ)=z := ⟨_,rfl⟩
  have j80_value : Bounds (-1/8 : ℝ) j80.value (-1/8 : ℝ) := by
    simpa only [← hj80,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/8 : ℝ))
  have j80_tangent : Bounds (0 : ℝ) j80.tangent (0 : ℝ) := by
    simpa only [← hj80,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v261 : ℝ := j52.value*j80.value
  have h261 : Bounds (1/128 : ℝ) v261 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j52_value j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v262 : ℝ := j52.tangent*j80.value
  have h262 : Bounds (-65/1024 : ℝ) v262 (-65/1024 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j52_tangent j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v263 : ℝ := j52.value*j80.tangent
  have h263 : Bounds (0 : ℝ) v263 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j52_value j80_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v264 : ℝ := v262+v263
  have h264 : Bounds (-65/1024 : ℝ) v264 (-65/1024 : ℝ) := by
    exact enlarge (IntervalBounds.add h262 h263) (by norm_num) (by norm_num)
  obtain ⟨j81,hj81⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j52 j80=z := ⟨_,rfl⟩
  have j81_value : Bounds (1/128 : ℝ) j81.value (1/128 : ℝ) := by
    simpa only [← hj81,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h261
  have j81_tangent : Bounds (-65/1024 : ℝ) j81.tangent (-65/1024 : ℝ) := by
    simpa only [← hj81,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h264
  let v265 : ℝ := j79.value+j81.value
  have h265 : Bounds (-127/256 : ℝ) v265 (-127/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j79_value j81_value) (by norm_num) (by norm_num)
  let v266 : ℝ := j79.tangent+j81.tangent
  have h266 : Bounds (-65/2048 : ℝ) v266 (-65/2048 : ℝ) := by
    exact enlarge (IntervalBounds.add j79_tangent j81_tangent) (by norm_num) (by norm_num)
  obtain ⟨j82,hj82⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j79 j81=z := ⟨_,rfl⟩
  have j82_value : Bounds (-127/256 : ℝ) j82.value (-127/256 : ℝ) := by
    simpa only [← hj82,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h265
  have j82_tangent : Bounds (-65/2048 : ℝ) j82.tangent (-65/2048 : ℝ) := by
    simpa only [← hj82,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h266
  let v267 : ℝ := j78.value*j82.value
  have h267 : Bounds (127/1024 : ℝ) v267 (127/1024 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j78_value j82_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v268 : ℝ := j78.tangent*j82.value
  have h268 : Bounds (0 : ℝ) v268 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j78_tangent j82_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v269 : ℝ := j78.value*j82.tangent
  have h269 : Bounds (65/8192 : ℝ) v269 (65/8192 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j78_value j82_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v270 : ℝ := v268+v269
  have h270 : Bounds (65/8192 : ℝ) v270 (65/8192 : ℝ) := by
    exact enlarge (IntervalBounds.add h268 h269) (by norm_num) (by norm_num)
  obtain ⟨j83,hj83⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j78 j82=z := ⟨_,rfl⟩
  have j83_value : Bounds (127/1024 : ℝ) j83.value (127/1024 : ℝ) := by
    simpa only [← hj83,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h267
  have j83_tangent : Bounds (65/8192 : ℝ) j83.tangent (65/8192 : ℝ) := by
    simpa only [← hj83,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h270
  let v271 : ℝ := j77.value*j83.value
  have h271 : Bounds (8176129946711/50000000000000 : ℝ) v271 (16352259893423/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v272 : ℝ := j77.tangent*j83.value
  have h272 : Bounds (0 : ℝ) v272 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v273 : ℝ := j77.value*j83.tangent
  have h273 : Bounds (1046158359323/100000000000000 : ℝ) v273 (261539589831/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v274 : ℝ := v272+v273
  have h274 : Bounds (1046158359323/100000000000000 : ℝ) v274 (261539589831/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h272 h273) (by norm_num) (by norm_num)
  obtain ⟨j84,hj84⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j83=z := ⟨_,rfl⟩
  have j84_value : Bounds (8176129946711/50000000000000 : ℝ) j84.value (16352259893423/100000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h271
  have j84_tangent : Bounds (1046158359323/100000000000000 : ℝ) j84.tangent (261539589831/25000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h274
  let v275 : ℝ := -(-1/8 : ℝ)
  have h275 : Bounds (1/8 : ℝ) v275 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (-1/8 : ℝ))) (by norm_num) (by norm_num)
  let v276 : ℝ := d+v275
  have h276 : Bounds (-3600928478703/4000000000000 : ℝ) v276 (-45011605983787/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hd h275) (by norm_num) (by norm_num)
  obtain ⟨j85,hj85⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (d+(-(-1/8 : ℝ)))=z := ⟨_,rfl⟩
  have j85_value : Bounds (-3600928478703/4000000000000 : ℝ) j85.value (-45011605983787/50000000000000 : ℝ) := by
    simpa only [← hj85,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h276
  have j85_tangent : Bounds (0 : ℝ) j85.tangent (0 : ℝ) := by
    simpa only [← hj85,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v277 : ℝ := j70.value*j4.value
  have h277 : Bounds (1/16 : ℝ) v277 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j70_value j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v278 : ℝ := j70.tangent*j4.value
  have h278 : Bounds (-65/128 : ℝ) v278 (-65/128 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j70_tangent j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v279 : ℝ := j70.value*j4.tangent
  have h279 : Bounds (0 : ℝ) v279 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j70_value j4_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v280 : ℝ := v278+v279
  have h280 : Bounds (-65/128 : ℝ) v280 (-65/128 : ℝ) := by
    exact enlarge (IntervalBounds.add h278 h279) (by norm_num) (by norm_num)
  obtain ⟨j86,hj86⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j70 j4=z := ⟨_,rfl⟩
  have j86_value : Bounds (1/16 : ℝ) j86.value (1/16 : ℝ) := by
    simpa only [← hj86,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h277
  have j86_tangent : Bounds (-65/128 : ℝ) j86.tangent (-65/128 : ℝ) := by
    simpa only [← hj86,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h280
  let v281 : ℝ := j76.value*j80.value
  have h281 : Bounds (-1/8 : ℝ) v281 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j76_value j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v282 : ℝ := j76.tangent*j80.value
  have h282 : Bounds (1/64 : ℝ) v282 (1/64 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j76_tangent j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v283 : ℝ := j76.value*j80.tangent
  have h283 : Bounds (0 : ℝ) v283 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j76_value j80_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v284 : ℝ := v282+v283
  have h284 : Bounds (1/64 : ℝ) v284 (1/64 : ℝ) := by
    exact enlarge (IntervalBounds.add h282 h283) (by norm_num) (by norm_num)
  obtain ⟨j87,hj87⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j76 j80=z := ⟨_,rfl⟩
  have j87_value : Bounds (-1/8 : ℝ) j87.value (-1/8 : ℝ) := by
    simpa only [← hj87,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h281
  have j87_tangent : Bounds (1/64 : ℝ) j87.tangent (1/64 : ℝ) := by
    simpa only [← hj87,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h284
  let v285 : ℝ := j86.value+j87.value
  have h285 : Bounds (-1/16 : ℝ) v285 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j86_value j87_value) (by norm_num) (by norm_num)
  let v286 : ℝ := j86.tangent+j87.tangent
  have h286 : Bounds (-63/128 : ℝ) v286 (-63/128 : ℝ) := by
    exact enlarge (IntervalBounds.add j86_tangent j87_tangent) (by norm_num) (by norm_num)
  obtain ⟨j88,hj88⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j86 j87=z := ⟨_,rfl⟩
  have j88_value : Bounds (-1/16 : ℝ) j88.value (-1/16 : ℝ) := by
    simpa only [← hj88,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h285
  have j88_tangent : Bounds (-63/128 : ℝ) j88.tangent (-63/128 : ℝ) := by
    simpa only [← hj88,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h286
  let v287 : ℝ := j78.value*j88.value
  have h287 : Bounds (1/64 : ℝ) v287 (1/64 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j78_value j88_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v288 : ℝ := j78.tangent*j88.value
  have h288 : Bounds (0 : ℝ) v288 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j78_tangent j88_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v289 : ℝ := j78.value*j88.tangent
  have h289 : Bounds (63/512 : ℝ) v289 (63/512 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j78_value j88_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v290 : ℝ := v288+v289
  have h290 : Bounds (63/512 : ℝ) v290 (63/512 : ℝ) := by
    exact enlarge (IntervalBounds.add h288 h289) (by norm_num) (by norm_num)
  obtain ⟨j89,hj89⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j78 j88=z := ⟨_,rfl⟩
  have j89_value : Bounds (1/64 : ℝ) j89.value (1/64 : ℝ) := by
    simpa only [← hj89,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h287
  have j89_tangent : Bounds (63/512 : ℝ) j89.tangent (63/512 : ℝ) := by
    simpa only [← hj89,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h290
  let v291 : ℝ := j85.value*j89.value
  have h291 : Bounds (-703306343497/50000000000000 : ℝ) v291 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v292 : ℝ := j85.tangent*j89.value
  have h292 : Bounds (0 : ℝ) v292 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v293 : ℝ := j85.value*j89.tangent
  have h293 : Bounds (-11077074910073/100000000000000 : ℝ) v293 (-1384634363759/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v294 : ℝ := v292+v293
  have h294 : Bounds (-11077074910073/100000000000000 : ℝ) v294 (-1384634363759/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h292 h293) (by norm_num) (by norm_num)
  obtain ⟨j90,hj90⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j89=z := ⟨_,rfl⟩
  have j90_value : Bounds (-703306343497/50000000000000 : ℝ) j90.value (-1406612686993/100000000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h291
  have j90_tangent : Bounds (-11077074910073/100000000000000 : ℝ) j90.tangent (-1384634363759/12500000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h294
  let v295 : ℝ := j84.value+j90.value
  have h295 : Bounds (3736411801607/25000000000000 : ℝ) v295 (1494564720643/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_value j90_value) (by norm_num) (by norm_num)
  let v296 : ℝ := j84.tangent+j90.tangent
  have h296 : Bounds (-40123666203/400000000000 : ℝ) v296 (-2507729137687/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_tangent j90_tangent) (by norm_num) (by norm_num)
  obtain ⟨j91,hj91⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j84 j90=z := ⟨_,rfl⟩
  have j91_value : Bounds (3736411801607/25000000000000 : ℝ) j91.value (1494564720643/10000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h295
  have j91_tangent : Bounds (-40123666203/400000000000 : ℝ) j91.tangent (-2507729137687/25000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h296
  let v297 : ℝ := j91.value⁻¹
  have h297 : Bounds (669091131476577/100000000000000 : ℝ) v297 (167272782869167/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j91_value (by norm_num)) (by norm_num) (by norm_num)
  let v298 : ℝ := -j91.tangent
  have h298 : Bounds (2507729137687/25000000000000 : ℝ) v298 (40123666203/400000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j91_tangent) (by norm_num) (by norm_num)
  let v299 : ℝ := j91.value*j91.value
  have h299 : Bounds (223372370419/10000000000000 : ℝ) v299 (2233723704191/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j91_value j91_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v300 : ℝ := v299⁻¹
  have h300 : Bounds (1119207355551361/25000000000000 : ℝ) v300 (4476829422207449/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h299 (by norm_num)) (by norm_num) (by norm_num)
  let v301 : ℝ := v298*v300
  have h301 : Bounds (449067023460761/100000000000000 : ℝ) v301 (449067023461053/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn h298 h300 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j92,hj92⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j91=z := ⟨_,rfl⟩
  have j92_value : Bounds (669091131476577/100000000000000 : ℝ) j92.value (167272782869167/25000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h297
  have j92_tangent : Bounds (449067023460761/100000000000000 : ℝ) j92.tangent (449067023461053/100000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h301
  let v302 : ℝ := j83.value*j77.value
  have h302 : Bounds (8176129946711/50000000000000 : ℝ) v302 (16352259893423/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v303 : ℝ := j83.tangent*j77.value
  have h303 : Bounds (1046158359323/100000000000000 : ℝ) v303 (261539589831/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v304 : ℝ := j83.value*j77.tangent
  have h304 : Bounds (0 : ℝ) v304 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v305 : ℝ := v303+v304
  have h305 : Bounds (1046158359323/100000000000000 : ℝ) v305 (261539589831/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h303 h304) (by norm_num) (by norm_num)
  obtain ⟨j93,hj93⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j77=z := ⟨_,rfl⟩
  have j93_value : Bounds (8176129946711/50000000000000 : ℝ) j93.value (16352259893423/100000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h302
  have j93_tangent : Bounds (1046158359323/100000000000000 : ℝ) j93.tangent (261539589831/25000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h305
  let v306 : ℝ := j92.value*j93.value
  have h306 : Bounds (109411520742887/100000000000000 : ℝ) v306 (10941152074291/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v307 : ℝ := j92.tangent*j93.value
  have h307 : Bounds (73432606771957/100000000000000 : ℝ) v307 (73432606772011/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v308 : ℝ := j92.value*j93.tangent
  have h308 : Bounds (6999752803431/100000000000000 : ℝ) v308 (6999752803439/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j93_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v309 : ℝ := v307+v308
  have h309 : Bounds (20108089893847/25000000000000 : ℝ) v309 (1608647191509/2000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h307 h308) (by norm_num) (by norm_num)
  obtain ⟨j94,hj94⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j93=z := ⟨_,rfl⟩
  have j94_value : Bounds (109411520742887/100000000000000 : ℝ) j94.value (10941152074291/10000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h306
  have j94_tangent : Bounds (20108089893847/25000000000000 : ℝ) j94.tangent (1608647191509/2000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h309
  let v310 : ℝ := -j94.value
  have h310 : Bounds (-10941152074291/10000000000000 : ℝ) v310 (-109411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_value) (by norm_num) (by norm_num)
  let v311 : ℝ := j0.value+v310
  have h311 : Bounds (-941152074291/10000000000000 : ℝ) v311 (-9411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h310) (by norm_num) (by norm_num)
  let v312 : ℝ := -j94.tangent
  have h312 : Bounds (-1608647191509/2000000000000 : ℝ) v312 (-20108089893847/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_tangent) (by norm_num) (by norm_num)
  let v313 : ℝ := j0.tangent+v312
  have h313 : Bounds (-1608647191509/2000000000000 : ℝ) v313 (-20108089893847/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h312) (by norm_num) (by norm_num)
  obtain ⟨j95,hj95⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j94=z := ⟨_,rfl⟩
  have j95_value : Bounds (-941152074291/10000000000000 : ℝ) j95.value (-9411520742887/100000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h311
  have j95_tangent : Bounds (-1608647191509/2000000000000 : ℝ) j95.tangent (-20108089893847/25000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h313
  let v314 : ℝ := j95.value*j41.value
  have h314 : Bounds (-4742524124357/100000000000000 : ℝ) v314 (-948504824869/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v315 : ℝ := j95.tangent*j41.value
  have h315 : Bounds (-40530368692317/100000000000000 : ℝ) v315 (-8106073738457/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v316 : ℝ := j95.value*j41.tangent
  have h316 : Bounds (298705492327/100000000000000 : ℝ) v316 (298705492329/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v317 : ℝ := v315+v316
  have h317 : Bounds (-4023166319999/10000000000000 : ℝ) v317 (-10057915799989/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h315 h316) (by norm_num) (by norm_num)
  obtain ⟨j96,hj96⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j41=z := ⟨_,rfl⟩
  have j96_value : Bounds (-4742524124357/100000000000000 : ℝ) j96.value (-948504824869/20000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h314
  have j96_tangent : Bounds (-4023166319999/10000000000000 : ℝ) j96.tangent (-10057915799989/25000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h317
  let v318 : ℝ := j83.value*j85.value
  have h318 : Bounds (-1116498820301/10000000000000 : ℝ) v318 (-11164988203009/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j83_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v319 : ℝ := j83.tangent*j85.value
  have h319 : Bounds (-357147752557/50000000000000 : ℝ) v319 (-714295505113/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j83_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v320 : ℝ := j83.value*j85.tangent
  have h320 : Bounds (0 : ℝ) v320 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v321 : ℝ := v319+v320
  have h321 : Bounds (-357147752557/50000000000000 : ℝ) v321 (-714295505113/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h319 h320) (by norm_num) (by norm_num)
  obtain ⟨j97,hj97⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j85=z := ⟨_,rfl⟩
  have j97_value : Bounds (-1116498820301/10000000000000 : ℝ) j97.value (-11164988203009/100000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h318
  have j97_tangent : Bounds (-357147752557/50000000000000 : ℝ) j97.tangent (-714295505113/100000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h321
  let v322 : ℝ := j92.value*j97.value
  have h322 : Bounds (-74703945896757/100000000000000 : ℝ) v322 (-74703945896739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v323 : ℝ := j92.tangent*j97.value
  have h323 : Bounds (-10027656038607/20000000000000 : ℝ) v323 (-50138280192997/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v324 : ℝ := j92.value*j97.tangent
  have h324 : Bounds (-955857575451/20000000000000 : ℝ) v324 (-2389643938623/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j97_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v325 : ℝ := v323+v324
  have h325 : Bounds (-5491756807029/10000000000000 : ℝ) v325 (-54917568070243/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h323 h324) (by norm_num) (by norm_num)
  obtain ⟨j98,hj98⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j97=z := ⟨_,rfl⟩
  have j98_value : Bounds (-74703945896757/100000000000000 : ℝ) j98.value (-74703945896739/100000000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h322
  have j98_tangent : Bounds (-5491756807029/10000000000000 : ℝ) j98.tangent (-54917568070243/100000000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h325
  let v326 : ℝ := -j98.value
  have h326 : Bounds (74703945896739/100000000000000 : ℝ) v326 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_value) (by norm_num) (by norm_num)
  let v327 : ℝ := j6.value+v326
  have h327 : Bounds (74703945896739/100000000000000 : ℝ) v327 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h326) (by norm_num) (by norm_num)
  let v328 : ℝ := -j98.tangent
  have h328 : Bounds (54917568070243/100000000000000 : ℝ) v328 (5491756807029/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_tangent) (by norm_num) (by norm_num)
  let v329 : ℝ := j6.tangent+v328
  have h329 : Bounds (54917568070243/100000000000000 : ℝ) v329 (5491756807029/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h328) (by norm_num) (by norm_num)
  obtain ⟨j99,hj99⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j98=z := ⟨_,rfl⟩
  have j99_value : Bounds (74703945896739/100000000000000 : ℝ) j99.value (74703945896757/100000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h327
  have j99_tangent : Bounds (54917568070243/100000000000000 : ℝ) j99.tangent (5491756807029/10000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h329
  let v330 : ℝ := j99.value*j70.value
  have h330 : Bounds (-1167249154637/25000000000000 : ℝ) v330 (-2334498309273/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v331 : ℝ := j99.tangent*j70.value
  have h331 : Bounds (-1716174002197/50000000000000 : ℝ) v331 (-343234800439/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v332 : ℝ := j99.value*j70.tangent
  have h332 : Bounds (37935597525687/100000000000000 : ℝ) v332 (37935597525697/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v333 : ℝ := v331+v332
  have h333 : Bounds (34503249521293/100000000000000 : ℝ) v333 (34503249521307/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h331 h332) (by norm_num) (by norm_num)
  obtain ⟨j100,hj100⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j70=z := ⟨_,rfl⟩
  have j100_value : Bounds (-1167249154637/25000000000000 : ℝ) j100.value (-2334498309273/50000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h330
  have j100_tangent : Bounds (34503249521293/100000000000000 : ℝ) j100.tangent (34503249521307/100000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h333
  let v334 : ℝ := j96.value+j100.value
  have h334 : Bounds (-1882304148581/20000000000000 : ℝ) v334 (-9411520742891/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_value j100_value) (by norm_num) (by norm_num)
  let v335 : ℝ := j96.tangent+j100.tangent
  have h335 : Bounds (-5728413678697/100000000000000 : ℝ) v335 (-5728413678649/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_tangent j100_tangent) (by norm_num) (by norm_num)
  obtain ⟨j101,hj101⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j96 j100=z := ⟨_,rfl⟩
  have j101_value : Bounds (-1882304148581/20000000000000 : ℝ) j101.value (-9411520742891/100000000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h334
  have j101_tangent : Bounds (-5728413678697/100000000000000 : ℝ) j101.tangent (-5728413678649/100000000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h335
  let v336 : ℝ := j92.value*j84.value
  have h336 : Bounds (109411520742887/100000000000000 : ℝ) v336 (10941152074291/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v337 : ℝ := j92.tangent*j84.value
  have h337 : Bounds (73432606771957/100000000000000 : ℝ) v337 (73432606772011/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v338 : ℝ := j92.value*j84.tangent
  have h338 : Bounds (6999752803431/100000000000000 : ℝ) v338 (6999752803439/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j84_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v339 : ℝ := v337+v338
  have h339 : Bounds (20108089893847/25000000000000 : ℝ) v339 (1608647191509/2000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h337 h338) (by norm_num) (by norm_num)
  obtain ⟨j102,hj102⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j84=z := ⟨_,rfl⟩
  have j102_value : Bounds (109411520742887/100000000000000 : ℝ) j102.value (10941152074291/10000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h336
  have j102_tangent : Bounds (20108089893847/25000000000000 : ℝ) j102.tangent (1608647191509/2000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h339
  let v340 : ℝ := -j102.value
  have h340 : Bounds (-10941152074291/10000000000000 : ℝ) v340 (-109411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_value) (by norm_num) (by norm_num)
  let v341 : ℝ := j0.value+v340
  have h341 : Bounds (-941152074291/10000000000000 : ℝ) v341 (-9411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h340) (by norm_num) (by norm_num)
  let v342 : ℝ := -j102.tangent
  have h342 : Bounds (-1608647191509/2000000000000 : ℝ) v342 (-20108089893847/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_tangent) (by norm_num) (by norm_num)
  let v343 : ℝ := j0.tangent+v342
  have h343 : Bounds (-1608647191509/2000000000000 : ℝ) v343 (-20108089893847/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h342) (by norm_num) (by norm_num)
  obtain ⟨j103,hj103⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j102=z := ⟨_,rfl⟩
  have j103_value : Bounds (-941152074291/10000000000000 : ℝ) j103.value (-9411520742887/100000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h341
  have j103_tangent : Bounds (-1608647191509/2000000000000 : ℝ) j103.tangent (-20108089893847/25000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h343
  let v344 : ℝ := j101.value*j103.value
  have h344 : Bounds (442883613469/50000000000000 : ℝ) v344 (442883613471/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v345 : ℝ := j101.tangent*j103.value
  have h345 : Bounds (134782710401/25000000000000 : ℝ) v345 (539130841611/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v346 : ℝ := j101.value*j103.tangent
  have h346 : Bounds (3784954102717/50000000000000 : ℝ) v346 (1892477051363/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v347 : ℝ := v345+v346
  have h347 : Bounds (4054519523519/50000000000000 : ℝ) v347 (8109039047063/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h345 h346) (by norm_num) (by norm_num)
  obtain ⟨j104,hj104⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j103=z := ⟨_,rfl⟩
  have j104_value : Bounds (442883613469/50000000000000 : ℝ) j104.value (442883613471/50000000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h344
  have j104_tangent : Bounds (4054519523519/50000000000000 : ℝ) j104.tangent (8109039047063/100000000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h347
  let v348 : ℝ := j95.value*j52.value
  have h348 : Bounds (58822004643/10000000000000 : ℝ) v348 (18381876451/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v349 : ℝ := j95.tangent*j52.value
  have h349 : Bounds (5027022473461/100000000000000 : ℝ) v349 (2513511236733/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v350 : ℝ := j95.value*j52.tangent
  have h350 : Bounds (-4779287877259/100000000000000 : ℝ) v350 (-4779287877247/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v351 : ℝ := v349+v350
  have h351 : Bounds (123867298101/50000000000000 : ℝ) v351 (247734596219/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h349 h350) (by norm_num) (by norm_num)
  obtain ⟨j105,hj105⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j52=z := ⟨_,rfl⟩
  have j105_value : Bounds (58822004643/10000000000000 : ℝ) j105.value (18381876451/3125000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h348
  have j105_tangent : Bounds (123867298101/50000000000000 : ℝ) j105.tangent (247734596219/100000000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h351
  let v352 : ℝ := j99.value*j76.value
  have h352 : Bounds (74703945896739/100000000000000 : ℝ) v352 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v353 : ℝ := j99.tangent*j76.value
  have h353 : Bounds (54917568070243/100000000000000 : ℝ) v353 (5491756807029/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v354 : ℝ := j99.value*j76.tangent
  have h354 : Bounds (-1867598647419/20000000000000 : ℝ) v354 (-2334498309273/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v355 : ℝ := v353+v354
  have h355 : Bounds (11394893708287/25000000000000 : ℝ) v355 (22789787416599/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h353 h354) (by norm_num) (by norm_num)
  obtain ⟨j106,hj106⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j76=z := ⟨_,rfl⟩
  have j106_value : Bounds (74703945896739/100000000000000 : ℝ) j106.value (74703945896757/100000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h352
  have j106_tangent : Bounds (11394893708287/25000000000000 : ℝ) j106.tangent (22789787416599/50000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h355
  let v356 : ℝ := j105.value+j106.value
  have h356 : Bounds (75292165943169/100000000000000 : ℝ) v356 (75292165943189/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_value j106_value) (by norm_num) (by norm_num)
  let v357 : ℝ := j105.tangent+j106.tangent
  have h357 : Bounds (916546188587/2000000000000 : ℝ) v357 (45827309429417/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_tangent j106_tangent) (by norm_num) (by norm_num)
  obtain ⟨j107,hj107⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j105 j106=z := ⟨_,rfl⟩
  have j107_value : Bounds (75292165943169/100000000000000 : ℝ) j107.value (75292165943189/100000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h356
  have j107_tangent : Bounds (916546188587/2000000000000 : ℝ) j107.tangent (45827309429417/100000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h357
  let v358 : ℝ := j85.value*j83.value
  have h358 : Bounds (-1116498820301/10000000000000 : ℝ) v358 (-11164988203009/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v359 : ℝ := j85.tangent*j83.value
  have h359 : Bounds (0 : ℝ) v359 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v360 : ℝ := j85.value*j83.tangent
  have h360 : Bounds (-357147752557/50000000000000 : ℝ) v360 (-714295505113/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v361 : ℝ := v359+v360
  have h361 : Bounds (-357147752557/50000000000000 : ℝ) v361 (-714295505113/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h359 h360) (by norm_num) (by norm_num)
  obtain ⟨j108,hj108⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j83=z := ⟨_,rfl⟩
  have j108_value : Bounds (-1116498820301/10000000000000 : ℝ) j108.value (-11164988203009/100000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h358
  have j108_tangent : Bounds (-357147752557/50000000000000 : ℝ) j108.tangent (-714295505113/100000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h361
  let v362 : ℝ := j92.value*j108.value
  have h362 : Bounds (-74703945896757/100000000000000 : ℝ) v362 (-74703945896739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v363 : ℝ := j92.tangent*j108.value
  have h363 : Bounds (-10027656038607/20000000000000 : ℝ) v363 (-50138280192997/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v364 : ℝ := j92.value*j108.tangent
  have h364 : Bounds (-955857575451/20000000000000 : ℝ) v364 (-2389643938623/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j108_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v365 : ℝ := v363+v364
  have h365 : Bounds (-5491756807029/10000000000000 : ℝ) v365 (-54917568070243/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h363 h364) (by norm_num) (by norm_num)
  obtain ⟨j109,hj109⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j108=z := ⟨_,rfl⟩
  have j109_value : Bounds (-74703945896757/100000000000000 : ℝ) j109.value (-74703945896739/100000000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h362
  have j109_tangent : Bounds (-5491756807029/10000000000000 : ℝ) j109.tangent (-54917568070243/100000000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h365
  let v366 : ℝ := -j109.value
  have h366 : Bounds (74703945896739/100000000000000 : ℝ) v366 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_value) (by norm_num) (by norm_num)
  let v367 : ℝ := j6.value+v366
  have h367 : Bounds (74703945896739/100000000000000 : ℝ) v367 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h366) (by norm_num) (by norm_num)
  let v368 : ℝ := -j109.tangent
  have h368 : Bounds (54917568070243/100000000000000 : ℝ) v368 (5491756807029/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_tangent) (by norm_num) (by norm_num)
  let v369 : ℝ := j6.tangent+v368
  have h369 : Bounds (54917568070243/100000000000000 : ℝ) v369 (5491756807029/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h368) (by norm_num) (by norm_num)
  obtain ⟨j110,hj110⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j109=z := ⟨_,rfl⟩
  have j110_value : Bounds (74703945896739/100000000000000 : ℝ) j110.value (74703945896757/100000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h367
  have j110_tangent : Bounds (54917568070243/100000000000000 : ℝ) j110.tangent (5491756807029/10000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h369
  let v370 : ℝ := j107.value*j110.value
  have h370 : Bounds (56246218910667/100000000000000 : ℝ) v370 (56246218910697/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v371 : ℝ := j107.tangent*j110.value
  have h371 : Bounds (2139675527627/6250000000000 : ℝ) v371 (8558702110523/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v372 : ℝ := j107.value*j110.tangent
  have h372 : Bounds (206743132417/500000000000 : ℝ) v372 (41348626483447/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v373 : ℝ := v371+v372
  have h373 : Bounds (9447929365679/12500000000000 : ℝ) v373 (75583434925539/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h371 h372) (by norm_num) (by norm_num)
  obtain ⟨j111,hj111⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j110=z := ⟨_,rfl⟩
  have j111_value : Bounds (56246218910667/100000000000000 : ℝ) j111.value (56246218910697/100000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h370
  have j111_tangent : Bounds (9447929365679/12500000000000 : ℝ) j111.tangent (75583434925539/100000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h373
  let v374 : ℝ := j104.value+j111.value
  have h374 : Bounds (11426397227521/20000000000000 : ℝ) v374 (57131986137639/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_value j111_value) (by norm_num) (by norm_num)
  let v375 : ℝ := j104.tangent+j111.tangent
  have h375 : Bounds (8369247397247/10000000000000 : ℝ) v375 (41846236986301/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_tangent j111_tangent) (by norm_num) (by norm_num)
  obtain ⟨j112,hj112⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j104 j111=z := ⟨_,rfl⟩
  have j112_value : Bounds (11426397227521/20000000000000 : ℝ) j112.value (57131986137639/100000000000000 : ℝ) := by
    simpa only [← hj112,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h374
  have j112_tangent : Bounds (8369247397247/10000000000000 : ℝ) j112.tangent (41846236986301/50000000000000 : ℝ) := by
    simpa only [← hj112,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h375
  let v376 : ℝ := j83.value*j83.value
  have h376 : Bounds (16129/1048576 : ℝ) v376 (16129/1048576 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v377 : ℝ := j83.tangent*j83.value
  have h377 : Bounds (8255/8388608 : ℝ) v377 (8255/8388608 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v378 : ℝ := j83.value*j83.tangent
  have h378 : Bounds (8255/8388608 : ℝ) v378 (8255/8388608 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v379 : ℝ := v377+v378
  have h379 : Bounds (8255/4194304 : ℝ) v379 (8255/4194304 : ℝ) := by
    exact enlarge (IntervalBounds.add h377 h378) (by norm_num) (by norm_num)
  obtain ⟨j113,hj113⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j83=z := ⟨_,rfl⟩
  have j113_value : Bounds (16129/1048576 : ℝ) j113.value (16129/1048576 : ℝ) := by
    simpa only [← hj113,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h376
  have j113_tangent : Bounds (8255/4194304 : ℝ) j113.tangent (8255/4194304 : ℝ) := by
    simpa only [← hj113,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h379
  let v380 : ℝ := j92.value*j113.value
  have h380 : Bounds (643239668583/6250000000000 : ℝ) v380 (1029183469733/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v381 : ℝ := j92.tangent*j113.value
  have h381 : Bounds (3453732500743/50000000000000 : ℝ) v381 (6907465001491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v382 : ℝ := j92.value*j113.tangent
  have h382 : Bounds (1316868612847/100000000000000 : ℝ) v382 (82304288303/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j113_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v383 : ℝ := v381+v382
  have h383 : Bounds (8224333614333/100000000000000 : ℝ) v383 (8224333614339/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h381 h382) (by norm_num) (by norm_num)
  obtain ⟨j114,hj114⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j113=z := ⟨_,rfl⟩
  have j114_value : Bounds (643239668583/6250000000000 : ℝ) j114.value (1029183469733/10000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h380
  have j114_tangent : Bounds (8224333614333/100000000000000 : ℝ) j114.tangent (8224333614339/100000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h383
  let v384 : ℝ := j112.value+j114.value
  have h384 : Bounds (67423820834933/100000000000000 : ℝ) v384 (67423820834969/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_value j114_value) (by norm_num) (by norm_num)
  let v385 : ℝ := j112.tangent+j114.tangent
  have h385 : Bounds (91916807586803/100000000000000 : ℝ) v385 (91916807586941/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_tangent j114_tangent) (by norm_num) (by norm_num)
  obtain ⟨j115,hj115⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j112 j114=z := ⟨_,rfl⟩
  have j115_value : Bounds (67423820834933/100000000000000 : ℝ) j115.value (67423820834969/100000000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h384
  have j115_tangent : Bounds (91916807586803/100000000000000 : ℝ) j115.tangent (91916807586941/100000000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h385
  let v386 : ℝ := j77.value*j89.value
  have h386 : Bounds (2060127230667/100000000000000 : ℝ) v386 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v387 : ℝ := j77.tangent*j89.value
  have h387 : Bounds (0 : ℝ) v387 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v388 : ℝ := j77.value*j89.tangent
  have h388 : Bounds (3244700388301/20000000000000 : ℝ) v388 (8111750970753/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v389 : ℝ := v387+v388
  have h389 : Bounds (3244700388301/20000000000000 : ℝ) v389 (8111750970753/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h387 h388) (by norm_num) (by norm_num)
  obtain ⟨j116,hj116⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j89=z := ⟨_,rfl⟩
  have j116_value : Bounds (2060127230667/100000000000000 : ℝ) j116.value (515031807667/25000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h386
  have j116_tangent : Bounds (3244700388301/20000000000000 : ℝ) j116.tangent (8111750970753/50000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h389
  let v390 : ℝ := j92.value*j116.value
  have h390 : Bounds (6892064298763/50000000000000 : ℝ) v390 (430754018673/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v391 : ℝ := j92.tangent*j116.value
  have h391 : Bounds (462567601713/5000000000000 : ℝ) v391 (289104751071/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v392 : ℝ := j92.value*j116.tangent
  have h392 : Bounds (5427500635277/5000000000000 : ℝ) v392 (54275006352781/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v393 : ℝ := v391+v392
  have h393 : Bounds (589006823699/500000000000 : ℝ) v393 (58900682369917/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h391 h392) (by norm_num) (by norm_num)
  obtain ⟨j117,hj117⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j116=z := ⟨_,rfl⟩
  have j117_value : Bounds (6892064298763/50000000000000 : ℝ) j117.value (430754018673/3125000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h390
  have j117_tangent : Bounds (589006823699/500000000000 : ℝ) j117.tangent (58900682369917/50000000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h393
  let v394 : ℝ := -j117.value
  have h394 : Bounds (-430754018673/3125000000000 : ℝ) v394 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_value) (by norm_num) (by norm_num)
  let v395 : ℝ := j6.value+v394
  have h395 : Bounds (-430754018673/3125000000000 : ℝ) v395 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h394) (by norm_num) (by norm_num)
  let v396 : ℝ := -j117.tangent
  have h396 : Bounds (-58900682369917/50000000000000 : ℝ) v396 (-589006823699/500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_tangent) (by norm_num) (by norm_num)
  let v397 : ℝ := j6.tangent+v396
  have h397 : Bounds (-58900682369917/50000000000000 : ℝ) v397 (-589006823699/500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h396) (by norm_num) (by norm_num)
  obtain ⟨j118,hj118⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j117=z := ⟨_,rfl⟩
  have j118_value : Bounds (-430754018673/3125000000000 : ℝ) j118.value (-6892064298763/50000000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h395
  have j118_tangent : Bounds (-58900682369917/50000000000000 : ℝ) j118.tangent (-589006823699/500000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h397
  let v398 : ℝ := j101.value*j118.value
  have h398 : Bounds (648648061091/50000000000000 : ℝ) v398 (648648061093/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v399 : ℝ := j101.tangent*j118.value
  have h399 : Bounds (789611908063/100000000000000 : ℝ) v399 (789611908071/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v400 : ℝ := j101.value*j118.tangent
  have h400 : Bounds (5543449938947/50000000000000 : ℝ) v400 (2217379975583/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v401 : ℝ := v399+v400
  have h401 : Bounds (11876511785957/100000000000000 : ℝ) v401 (5938255892993/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h399 h400) (by norm_num) (by norm_num)
  obtain ⟨j119,hj119⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j118=z := ⟨_,rfl⟩
  have j119_value : Bounds (648648061091/50000000000000 : ℝ) j119.value (648648061093/50000000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h398
  have j119_tangent : Bounds (11876511785957/100000000000000 : ℝ) j119.tangent (5938255892993/50000000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h401
  let v402 : ℝ := j92.value*j90.value
  have h402 : Bounds (-9411520742903/100000000000000 : ℝ) v402 (-4705760371447/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v403 : ℝ := j92.tangent*j90.value
  have h403 : Bounds (-631663372511/10000000000000 : ℝ) v403 (-63166337251/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v404 : ℝ := j92.value*j90.tangent
  have h404 : Bounds (-37057862925163/50000000000000 : ℝ) v404 (-18528931462577/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v405 : ℝ := v403+v404
  have h405 : Bounds (-20108089893859/25000000000000 : ℝ) v405 (-5027022473463/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h403 h404) (by norm_num) (by norm_num)
  obtain ⟨j120,hj120⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j90=z := ⟨_,rfl⟩
  have j120_value : Bounds (-9411520742903/100000000000000 : ℝ) j120.value (-4705760371447/50000000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h402
  have j120_tangent : Bounds (-20108089893859/25000000000000 : ℝ) j120.tangent (-5027022473463/6250000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h405
  let v406 : ℝ := -j120.value
  have h406 : Bounds (4705760371447/50000000000000 : ℝ) v406 (9411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_value) (by norm_num) (by norm_num)
  let v407 : ℝ := j0.value+v406
  have h407 : Bounds (54705760371447/50000000000000 : ℝ) v407 (109411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h406) (by norm_num) (by norm_num)
  let v408 : ℝ := -j120.tangent
  have h408 : Bounds (5027022473463/6250000000000 : ℝ) v408 (20108089893859/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_tangent) (by norm_num) (by norm_num)
  let v409 : ℝ := j0.tangent+v408
  have h409 : Bounds (5027022473463/6250000000000 : ℝ) v409 (20108089893859/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h408) (by norm_num) (by norm_num)
  obtain ⟨j121,hj121⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j120=z := ⟨_,rfl⟩
  have j121_value : Bounds (54705760371447/50000000000000 : ℝ) j121.value (109411520742903/100000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h407
  have j121_tangent : Bounds (5027022473463/6250000000000 : ℝ) j121.tangent (20108089893859/25000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h409
  let v410 : ℝ := j107.value*j121.value
  have h410 : Bounds (20594575939671/25000000000000 : ℝ) v410 (41189151879357/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v411 : ℝ := j107.tangent*j121.value
  have h411 : Bounds (50140356162203/100000000000000 : ℝ) v411 (50140356162281/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v412 : ℝ := j107.value*j121.tangent
  have h412 : Bounds (30279632821761/50000000000000 : ℝ) v412 (1513981641089/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v413 : ℝ := v411+v412
  have h413 : Bounds (4427984872229/4000000000000 : ℝ) v413 (110699621805841/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h411 h412) (by norm_num) (by norm_num)
  obtain ⟨j122,hj122⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j121=z := ⟨_,rfl⟩
  have j122_value : Bounds (20594575939671/25000000000000 : ℝ) j122.value (41189151879357/50000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h410
  have j122_tangent : Bounds (4427984872229/4000000000000 : ℝ) j122.tangent (110699621805841/100000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h413
  let v414 : ℝ := j119.value+j122.value
  have h414 : Bounds (41837799940433/50000000000000 : ℝ) v414 (836755998809/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_value j122_value) (by norm_num) (by norm_num)
  let v415 : ℝ := j119.tangent+j122.tangent
  have h415 : Bounds (61288066795841/50000000000000 : ℝ) v415 (122576133591827/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_tangent j122_tangent) (by norm_num) (by norm_num)
  obtain ⟨j123,hj123⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j119 j122=z := ⟨_,rfl⟩
  have j123_value : Bounds (41837799940433/50000000000000 : ℝ) j123.value (836755998809/1000000000000 : ℝ) := by
    simpa only [← hj123,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h414
  have j123_tangent : Bounds (61288066795841/50000000000000 : ℝ) j123.tangent (122576133591827/100000000000000 : ℝ) := by
    simpa only [← hj123,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h415
  let v416 : ℝ := j83.value*j89.value
  have h416 : Bounds (127/65536 : ℝ) v416 (127/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v417 : ℝ := j83.tangent*j89.value
  have h417 : Bounds (65/524288 : ℝ) v417 (65/524288 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v418 : ℝ := j83.value*j89.tangent
  have h418 : Bounds (8001/524288 : ℝ) v418 (8001/524288 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v419 : ℝ := v417+v418
  have h419 : Bounds (4033/262144 : ℝ) v419 (4033/262144 : ℝ) := by
    exact enlarge (IntervalBounds.add h417 h418) (by norm_num) (by norm_num)
  obtain ⟨j124,hj124⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j89=z := ⟨_,rfl⟩
  have j124_value : Bounds (127/65536 : ℝ) j124.value (127/65536 : ℝ) := by
    simpa only [← hj124,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h416
  have j124_tangent : Bounds (4033/262144 : ℝ) j124.tangent (4033/262144 : ℝ) := by
    simpa only [← hj124,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h419
  let v420 : ℝ := j92.value*j124.value
  have h420 : Bounds (648304547863/50000000000000 : ℝ) v420 (1296609095727/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v421 : ℝ := j92.tangent*j124.value
  have h421 : Bounds (87023181121/10000000000000 : ℝ) v421 (217557952803/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v422 : ℝ := j92.value*j124.tangent
  have h422 : Bounds (1029374898241/10000000000000 : ℝ) v422 (2573437245603/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v423 : ℝ := v421+v422
  have h423 : Bounds (558199039681/5000000000000 : ℝ) v423 (1395497599203/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h421 h422) (by norm_num) (by norm_num)
  obtain ⟨j125,hj125⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j124=z := ⟨_,rfl⟩
  have j125_value : Bounds (648304547863/50000000000000 : ℝ) j125.value (1296609095727/100000000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h420
  have j125_tangent : Bounds (558199039681/5000000000000 : ℝ) j125.tangent (1395497599203/12500000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h423
  let v424 : ℝ := j123.value+j125.value
  have h424 : Bounds (5310763061037/6250000000000 : ℝ) v424 (84972208976627/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_value j125_value) (by norm_num) (by norm_num)
  let v425 : ℝ := j123.tangent+j125.tangent
  have h425 : Bounds (66870057192651/50000000000000 : ℝ) v425 (133740114385451/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_tangent j125_tangent) (by norm_num) (by norm_num)
  obtain ⟨j126,hj126⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j123 j125=z := ⟨_,rfl⟩
  have j126_value : Bounds (5310763061037/6250000000000 : ℝ) j126.value (84972208976627/100000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h424
  have j126_tangent : Bounds (66870057192651/50000000000000 : ℝ) j126.tangent (133740114385451/100000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h425
  let v426 : ℝ := j89.value*j77.value
  have h426 : Bounds (2060127230667/100000000000000 : ℝ) v426 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v427 : ℝ := j89.tangent*j77.value
  have h427 : Bounds (3244700388301/20000000000000 : ℝ) v427 (8111750970753/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v428 : ℝ := j89.value*j77.tangent
  have h428 : Bounds (0 : ℝ) v428 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v429 : ℝ := v427+v428
  have h429 : Bounds (3244700388301/20000000000000 : ℝ) v429 (8111750970753/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h427 h428) (by norm_num) (by norm_num)
  obtain ⟨j127,hj127⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j77=z := ⟨_,rfl⟩
  have j127_value : Bounds (2060127230667/100000000000000 : ℝ) j127.value (515031807667/25000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h426
  have j127_tangent : Bounds (3244700388301/20000000000000 : ℝ) j127.tangent (8111750970753/50000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h429
  let v430 : ℝ := j92.value*j127.value
  have h430 : Bounds (6892064298763/50000000000000 : ℝ) v430 (430754018673/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v431 : ℝ := j92.tangent*j127.value
  have h431 : Bounds (462567601713/5000000000000 : ℝ) v431 (289104751071/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v432 : ℝ := j92.value*j127.tangent
  have h432 : Bounds (5427500635277/5000000000000 : ℝ) v432 (54275006352781/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v433 : ℝ := v431+v432
  have h433 : Bounds (589006823699/500000000000 : ℝ) v433 (58900682369917/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h431 h432) (by norm_num) (by norm_num)
  obtain ⟨j128,hj128⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j127=z := ⟨_,rfl⟩
  have j128_value : Bounds (6892064298763/50000000000000 : ℝ) j128.value (430754018673/3125000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h430
  have j128_tangent : Bounds (589006823699/500000000000 : ℝ) j128.tangent (58900682369917/50000000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h433
  let v434 : ℝ := -j128.value
  have h434 : Bounds (-430754018673/3125000000000 : ℝ) v434 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_value) (by norm_num) (by norm_num)
  let v435 : ℝ := j6.value+v434
  have h435 : Bounds (-430754018673/3125000000000 : ℝ) v435 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h434) (by norm_num) (by norm_num)
  let v436 : ℝ := -j128.tangent
  have h436 : Bounds (-58900682369917/50000000000000 : ℝ) v436 (-589006823699/500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_tangent) (by norm_num) (by norm_num)
  let v437 : ℝ := j6.tangent+v436
  have h437 : Bounds (-58900682369917/50000000000000 : ℝ) v437 (-589006823699/500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h436) (by norm_num) (by norm_num)
  obtain ⟨j129,hj129⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j128=z := ⟨_,rfl⟩
  have j129_value : Bounds (-430754018673/3125000000000 : ℝ) j129.value (-6892064298763/50000000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h435
  have j129_tangent : Bounds (-58900682369917/50000000000000 : ℝ) j129.tangent (-589006823699/500000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h437
  let v438 : ℝ := j129.value*j41.value
  have h438 : Bounds (-6945908551103/100000000000000 : ℝ) v438 (-6945908551097/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v439 : ℝ := j129.tangent*j41.value
  have h439 : Bounds (-14840210987733/25000000000000 : ℝ) v439 (-29680421975457/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v440 : ℝ := j129.value*j41.tangent
  have h440 : Bounds (218742275107/50000000000000 : ℝ) v440 (87496910043/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v441 : ℝ := v439+v440
  have h441 : Bounds (-29461679700359/50000000000000 : ℝ) v441 (-58923359400699/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h439 h440) (by norm_num) (by norm_num)
  obtain ⟨j130,hj130⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j41=z := ⟨_,rfl⟩
  have j130_value : Bounds (-6945908551103/100000000000000 : ℝ) j130.value (-6945908551097/100000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h438
  have j130_tangent : Bounds (-29461679700359/50000000000000 : ℝ) j130.tangent (-58923359400699/100000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h441
  let v442 : ℝ := j89.value*j85.value
  have h442 : Bounds (-703306343497/50000000000000 : ℝ) v442 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v443 : ℝ := j89.tangent*j85.value
  have h443 : Bounds (-11077074910073/100000000000000 : ℝ) v443 (-1384634363759/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v444 : ℝ := j89.value*j85.tangent
  have h444 : Bounds (0 : ℝ) v444 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v445 : ℝ := v443+v444
  have h445 : Bounds (-11077074910073/100000000000000 : ℝ) v445 (-1384634363759/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h443 h444) (by norm_num) (by norm_num)
  obtain ⟨j131,hj131⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j85=z := ⟨_,rfl⟩
  have j131_value : Bounds (-703306343497/50000000000000 : ℝ) j131.value (-1406612686993/100000000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h442
  have j131_tangent : Bounds (-11077074910073/100000000000000 : ℝ) j131.tangent (-1384634363759/12500000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h445
  let v446 : ℝ := j92.value*j131.value
  have h446 : Bounds (-9411520742903/100000000000000 : ℝ) v446 (-4705760371447/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v447 : ℝ := j92.tangent*j131.value
  have h447 : Bounds (-631663372511/10000000000000 : ℝ) v447 (-63166337251/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v448 : ℝ := j92.value*j131.tangent
  have h448 : Bounds (-37057862925163/50000000000000 : ℝ) v448 (-18528931462577/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v449 : ℝ := v447+v448
  have h449 : Bounds (-20108089893859/25000000000000 : ℝ) v449 (-5027022473463/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h447 h448) (by norm_num) (by norm_num)
  obtain ⟨j132,hj132⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j131=z := ⟨_,rfl⟩
  have j132_value : Bounds (-9411520742903/100000000000000 : ℝ) j132.value (-4705760371447/50000000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h446
  have j132_tangent : Bounds (-20108089893859/25000000000000 : ℝ) j132.tangent (-5027022473463/6250000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h449
  let v450 : ℝ := -j132.value
  have h450 : Bounds (4705760371447/50000000000000 : ℝ) v450 (9411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_value) (by norm_num) (by norm_num)
  let v451 : ℝ := j0.value+v450
  have h451 : Bounds (54705760371447/50000000000000 : ℝ) v451 (109411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h450) (by norm_num) (by norm_num)
  let v452 : ℝ := -j132.tangent
  have h452 : Bounds (5027022473463/6250000000000 : ℝ) v452 (20108089893859/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_tangent) (by norm_num) (by norm_num)
  let v453 : ℝ := j0.tangent+v452
  have h453 : Bounds (5027022473463/6250000000000 : ℝ) v453 (20108089893859/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h452) (by norm_num) (by norm_num)
  obtain ⟨j133,hj133⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j132=z := ⟨_,rfl⟩
  have j133_value : Bounds (54705760371447/50000000000000 : ℝ) j133.value (109411520742903/100000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h451
  have j133_tangent : Bounds (5027022473463/6250000000000 : ℝ) j133.tangent (20108089893859/25000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h453
  let v454 : ℝ := j133.value*j70.value
  have h454 : Bounds (-213694376451/3125000000000 : ℝ) v454 (-683822004643/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v455 : ℝ := j133.tangent*j70.value
  have h455 : Bounds (-1005404494693/20000000000000 : ℝ) v455 (-5027022473463/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v456 : ℝ := j133.value*j70.tangent
  have h456 : Bounds (222242151509/400000000000 : ℝ) v456 (6945067234657/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v457 : ℝ := v455+v456
  have h457 : Bounds (10106703080757/20000000000000 : ℝ) v457 (50533515403793/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h455 h456) (by norm_num) (by norm_num)
  obtain ⟨j134,hj134⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j70=z := ⟨_,rfl⟩
  have j134_value : Bounds (-213694376451/3125000000000 : ℝ) j134.value (-683822004643/10000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h454
  have j134_tangent : Bounds (10106703080757/20000000000000 : ℝ) j134.tangent (50533515403793/100000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h457
  let v458 : ℝ := j130.value+j134.value
  have h458 : Bounds (-2756825719507/20000000000000 : ℝ) v458 (-13784128597527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_value j134_value) (by norm_num) (by norm_num)
  let v459 : ℝ := j130.tangent+j134.tangent
  have h459 : Bounds (-8389843996933/100000000000000 : ℝ) v459 (-4194921998453/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_tangent j134_tangent) (by norm_num) (by norm_num)
  obtain ⟨j135,hj135⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j130 j134=z := ⟨_,rfl⟩
  have j135_value : Bounds (-2756825719507/20000000000000 : ℝ) j135.value (-13784128597527/100000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h458
  have j135_tangent : Bounds (-8389843996933/100000000000000 : ℝ) j135.tangent (-4194921998453/50000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h459
  let v460 : ℝ := j135.value*j103.value
  have h460 : Bounds (648648061091/50000000000000 : ℝ) v460 (1297296122187/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v461 : ℝ := j135.tangent*j103.value
  have h461 : Bounds (24675372127/3125000000000 : ℝ) v461 (78961190807/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v462 : ℝ := j135.value*j103.tangent
  have h462 : Bounds (1385862484737/12500000000000 : ℝ) v462 (1385862484739/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v463 : ℝ := v461+v462
  have h463 : Bounds (296912794649/2500000000000 : ℝ) v463 (5938255892991/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h461 h462) (by norm_num) (by norm_num)
  obtain ⟨j136,hj136⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j103=z := ⟨_,rfl⟩
  have j136_value : Bounds (648648061091/50000000000000 : ℝ) j136.value (1297296122187/100000000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h460
  have j136_tangent : Bounds (296912794649/2500000000000 : ℝ) j136.tangent (5938255892991/50000000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h463
  let v464 : ℝ := j129.value*j52.value
  have h464 : Bounds (172301607469/20000000000000 : ℝ) v464 (430754018673/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v465 : ℝ := j129.tangent*j52.value
  have h465 : Bounds (7362585296237/100000000000000 : ℝ) v465 (92032316203/1250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v466 : ℝ := j129.value*j52.tangent
  have h466 : Bounds (-6999752803437/100000000000000 : ℝ) v466 (-6999752803431/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v467 : ℝ := v465+v466
  have h467 : Bounds (56692577/15625000000 : ℝ) v467 (362832492809/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h465 h466) (by norm_num) (by norm_num)
  obtain ⟨j137,hj137⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j52=z := ⟨_,rfl⟩
  have j137_value : Bounds (172301607469/20000000000000 : ℝ) j137.value (430754018673/50000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h464
  have j137_tangent : Bounds (56692577/15625000000 : ℝ) j137.tangent (362832492809/100000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h467
  let v468 : ℝ := j133.value*j76.value
  have h468 : Bounds (54705760371447/50000000000000 : ℝ) v468 (109411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v469 : ℝ := j133.tangent*j76.value
  have h469 : Bounds (5027022473463/6250000000000 : ℝ) v469 (20108089893859/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v470 : ℝ := j133.value*j76.tangent
  have h470 : Bounds (-13676440092863/100000000000000 : ℝ) v470 (-13676440092861/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v471 : ℝ := v469+v470
  have h471 : Bounds (13351183896509/20000000000000 : ℝ) v471 (2670236779303/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h469 h470) (by norm_num) (by norm_num)
  obtain ⟨j138,hj138⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j76=z := ⟨_,rfl⟩
  have j138_value : Bounds (54705760371447/50000000000000 : ℝ) j138.value (109411520742903/100000000000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h468
  have j138_tangent : Bounds (13351183896509/20000000000000 : ℝ) j138.tangent (2670236779303/4000000000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h471
  let v472 : ℝ := j137.value+j138.value
  have h472 : Bounds (110273028780239/100000000000000 : ℝ) v472 (110273028780249/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_value j138_value) (by norm_num) (by norm_num)
  let v473 : ℝ := j137.tangent+j138.tangent
  have h473 : Bounds (13423750395069/20000000000000 : ℝ) v473 (8389843996923/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_tangent j138_tangent) (by norm_num) (by norm_num)
  obtain ⟨j139,hj139⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j137 j138=z := ⟨_,rfl⟩
  have j139_value : Bounds (110273028780239/100000000000000 : ℝ) j139.value (110273028780249/100000000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h472
  have j139_tangent : Bounds (13423750395069/20000000000000 : ℝ) j139.tangent (8389843996923/12500000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h473
  let v474 : ℝ := j139.value*j110.value
  have h474 : Bounds (16475660751737/20000000000000 : ℝ) v474 (82378303758713/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v475 : ℝ := j139.tangent*j110.value
  have h475 : Bounds (12535089040557/25000000000000 : ℝ) v475 (5014035616227/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v476 : ℝ := j139.value*j110.tangent
  have h476 : Bounds (30279632821753/50000000000000 : ℝ) v476 (15139816410891/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v477 : ℝ := v475+v476
  have h477 : Bounds (55349810902867/50000000000000 : ℝ) v477 (55349810902917/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h475 h476) (by norm_num) (by norm_num)
  obtain ⟨j140,hj140⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j110=z := ⟨_,rfl⟩
  have j140_value : Bounds (16475660751737/20000000000000 : ℝ) j140.value (82378303758713/100000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h474
  have j140_tangent : Bounds (55349810902867/50000000000000 : ℝ) j140.tangent (55349810902917/50000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h477
  let v478 : ℝ := j136.value+j140.value
  have h478 : Bounds (83675599880867/100000000000000 : ℝ) v478 (836755998809/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_value j140_value) (by norm_num) (by norm_num)
  let v479 : ℝ := j136.tangent+j140.tangent
  have h479 : Bounds (61288066795847/50000000000000 : ℝ) v479 (15322016698977/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_tangent j140_tangent) (by norm_num) (by norm_num)
  obtain ⟨j141,hj141⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j136 j140=z := ⟨_,rfl⟩
  have j141_value : Bounds (83675599880867/100000000000000 : ℝ) j141.value (836755998809/1000000000000 : ℝ) := by
    simpa only [← hj141,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h478
  have j141_tangent : Bounds (61288066795847/50000000000000 : ℝ) j141.tangent (15322016698977/12500000000000 : ℝ) := by
    simpa only [← hj141,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h479
  let v480 : ℝ := j89.value*j83.value
  have h480 : Bounds (127/65536 : ℝ) v480 (127/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v481 : ℝ := j89.tangent*j83.value
  have h481 : Bounds (8001/524288 : ℝ) v481 (8001/524288 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v482 : ℝ := j89.value*j83.tangent
  have h482 : Bounds (65/524288 : ℝ) v482 (65/524288 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v483 : ℝ := v481+v482
  have h483 : Bounds (4033/262144 : ℝ) v483 (4033/262144 : ℝ) := by
    exact enlarge (IntervalBounds.add h481 h482) (by norm_num) (by norm_num)
  obtain ⟨j142,hj142⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j83=z := ⟨_,rfl⟩
  have j142_value : Bounds (127/65536 : ℝ) j142.value (127/65536 : ℝ) := by
    simpa only [← hj142,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h480
  have j142_tangent : Bounds (4033/262144 : ℝ) j142.tangent (4033/262144 : ℝ) := by
    simpa only [← hj142,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h483
  let v484 : ℝ := j92.value*j142.value
  have h484 : Bounds (648304547863/50000000000000 : ℝ) v484 (1296609095727/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v485 : ℝ := j92.tangent*j142.value
  have h485 : Bounds (87023181121/10000000000000 : ℝ) v485 (217557952803/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v486 : ℝ := j92.value*j142.tangent
  have h486 : Bounds (1029374898241/10000000000000 : ℝ) v486 (2573437245603/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v487 : ℝ := v485+v486
  have h487 : Bounds (558199039681/5000000000000 : ℝ) v487 (1395497599203/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h485 h486) (by norm_num) (by norm_num)
  obtain ⟨j143,hj143⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j142=z := ⟨_,rfl⟩
  have j143_value : Bounds (648304547863/50000000000000 : ℝ) j143.value (1296609095727/100000000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h484
  have j143_tangent : Bounds (558199039681/5000000000000 : ℝ) j143.tangent (1395497599203/12500000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h487
  let v488 : ℝ := j141.value+j143.value
  have h488 : Bounds (84972208976593/100000000000000 : ℝ) v488 (84972208976627/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_value j143_value) (by norm_num) (by norm_num)
  let v489 : ℝ := j141.tangent+j143.tangent
  have h489 : Bounds (66870057192657/50000000000000 : ℝ) v489 (835875714909/625000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_tangent j143_tangent) (by norm_num) (by norm_num)
  obtain ⟨j144,hj144⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j141 j143=z := ⟨_,rfl⟩
  have j144_value : Bounds (84972208976593/100000000000000 : ℝ) j144.value (84972208976627/100000000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h488
  have j144_tangent : Bounds (66870057192657/50000000000000 : ℝ) j144.tangent (835875714909/625000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h489
  let v490 : ℝ := j135.value*j118.value
  have h490 : Bounds (1900022011931/100000000000000 : ℝ) v490 (950011005967/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v491 : ℝ := j135.tangent*j118.value
  have h491 : Bounds (231293377133/20000000000000 : ℝ) v491 (115646688567/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v492 : ℝ := j135.value*j118.tangent
  have h492 : Bounds (129903132843/800000000000 : ℝ) v492 (1623789160539/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v493 : ℝ := v491+v492
  have h493 : Bounds (108714740569/625000000000 : ℝ) v493 (869717924553/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h491 h492) (by norm_num) (by norm_num)
  obtain ⟨j145,hj145⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j118=z := ⟨_,rfl⟩
  have j145_value : Bounds (1900022011931/100000000000000 : ℝ) j145.value (950011005967/50000000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h490
  have j145_tangent : Bounds (108714740569/625000000000 : ℝ) j145.tangent (869717924553/5000000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h493
  let v494 : ℝ := j139.value*j121.value
  have h494 : Bounds (30162849439427/25000000000000 : ℝ) v494 (12065139775773/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v495 : ℝ := j139.tangent*j121.value
  have h495 : Bounds (18358911809969/25000000000000 : ℝ) v495 (2937425889597/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v496 : ℝ := j139.value*j121.tangent
  have h496 : Bounds (44347599511607/50000000000000 : ℝ) v496 (44347599511627/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v497 : ℝ := v495+v496
  have h497 : Bounds (16213084626309/10000000000000 : ℝ) v497 (162130846263179/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h495 h496) (by norm_num) (by norm_num)
  obtain ⟨j146,hj146⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j121=z := ⟨_,rfl⟩
  have j146_value : Bounds (30162849439427/25000000000000 : ℝ) j146.value (12065139775773/10000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h494
  have j146_tangent : Bounds (16213084626309/10000000000000 : ℝ) j146.tangent (162130846263179/100000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h497
  let v498 : ℝ := j145.value+j146.value
  have h498 : Bounds (122551419769639/100000000000000 : ℝ) v498 (1914865933901/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_value j146_value) (by norm_num) (by norm_num)
  let v499 : ℝ := j145.tangent+j146.tangent
  have h499 : Bounds (17952520475413/10000000000000 : ℝ) v499 (179525204754239/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_tangent j146_tangent) (by norm_num) (by norm_num)
  obtain ⟨j147,hj147⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j145 j146=z := ⟨_,rfl⟩
  have j147_value : Bounds (122551419769639/100000000000000 : ℝ) j147.value (1914865933901/1562500000000 : ℝ) := by
    simpa only [← hj147,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h498
  have j147_tangent : Bounds (17952520475413/10000000000000 : ℝ) j147.tangent (179525204754239/100000000000000 : ℝ) := by
    simpa only [← hj147,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h499
  let v500 : ℝ := j89.value*j89.value
  have h500 : Bounds (1/4096 : ℝ) v500 (1/4096 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v501 : ℝ := j89.tangent*j89.value
  have h501 : Bounds (63/32768 : ℝ) v501 (63/32768 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v502 : ℝ := j89.value*j89.tangent
  have h502 : Bounds (63/32768 : ℝ) v502 (63/32768 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v503 : ℝ := v501+v502
  have h503 : Bounds (63/16384 : ℝ) v503 (63/16384 : ℝ) := by
    exact enlarge (IntervalBounds.add h501 h502) (by norm_num) (by norm_num)
  obtain ⟨j148,hj148⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j89=z := ⟨_,rfl⟩
  have j148_value : Bounds (1/4096 : ℝ) j148.value (1/4096 : ℝ) := by
    simpa only [← hj148,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h500
  have j148_tangent : Bounds (63/16384 : ℝ) j148.tangent (63/16384 : ℝ) := by
    simpa only [← hj148,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h503
  let v504 : ℝ := j92.value*j148.value
  have h504 : Bounds (8167616351/5000000000000 : ℝ) v504 (163352327021/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v505 : ℝ := j92.tangent*j148.value
  have h505 : Bounds (54817751887/50000000000000 : ℝ) v505 (4385420151/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v506 : ℝ := j92.value*j148.tangent
  have h506 : Bounds (102911966023/4000000000000 : ℝ) v506 (160799946911/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v507 : ℝ := v505+v506
  have h507 : Bounds (2682434654349/100000000000000 : ℝ) v507 (2682434654351/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h505 h506) (by norm_num) (by norm_num)
  obtain ⟨j149,hj149⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j148=z := ⟨_,rfl⟩
  have j149_value : Bounds (8167616351/5000000000000 : ℝ) j149.value (163352327021/100000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h504
  have j149_tangent : Bounds (2682434654349/100000000000000 : ℝ) j149.tangent (2682434654351/100000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h507
  let v508 : ℝ := j147.value+j149.value
  have h508 : Bounds (122714772096659/100000000000000 : ℝ) v508 (24542954419337/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_value j149_value) (by norm_num) (by norm_num)
  let v509 : ℝ := j147.tangent+j149.tangent
  have h509 : Bounds (182207639408479/100000000000000 : ℝ) v509 (18220763940859/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_tangent j149_tangent) (by norm_num) (by norm_num)
  obtain ⟨j150,hj150⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j147 j149=z := ⟨_,rfl⟩
  have j150_value : Bounds (122714772096659/100000000000000 : ℝ) j150.value (24542954419337/20000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h508
  have j150_tangent : Bounds (182207639408479/100000000000000 : ℝ) j150.tangent (18220763940859/10000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h509
  have hm02 : jetIter c d 0 2=!![j115,j126;j144,j150] := by
    rw [jetIter,hm01]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj79,← hj80,← hj81,← hj82,← hj83,← hj84,← hj85,← hj86,← hj87,← hj88,← hj89,← hj90,← hj91,← hj92,← hj93,← hj94,← hj95,← hj96,← hj97,← hj98,← hj99,← hj100,← hj101,← hj102,← hj103,← hj104,← hj105,← hj106,← hj107,← hj108,← hj109,← hj110,← hj111,← hj112,← hj113,← hj114,← hj115,← hj116,← hj117,← hj118,← hj119,← hj120,← hj121,← hj122,← hj123,← hj124,← hj125,← hj126,← hj127,← hj128,← hj129,← hj130,← hj131,← hj132,← hj133,← hj134,← hj135,← hj136,← hj137,← hj138,← hj139,← hj140,← hj141,← hj142,← hj143,← hj144,← hj145,← hj146,← hj147,← hj148,← hj149,← hj150]
    all_goals rfl
  let v510 : ℝ := -c
  have h510 : Bounds (-318481427627119/1000000000000000 : ℝ) v510 (-159240713813559/500000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hc) (by norm_num) (by norm_num)
  let v511 : ℝ := (1 : ℝ)+v510
  have h511 : Bounds (8518982154661/12500000000000 : ℝ) v511 (68151857237289/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (1 : ℝ)) h510) (by norm_num) (by norm_num)
  obtain ⟨j151,hj151⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((1 : ℝ)+(-c))=z := ⟨_,rfl⟩
  have j151_value : Bounds (8518982154661/12500000000000 : ℝ) j151.value (68151857237289/100000000000000 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h511
  have j151_tangent : Bounds (0 : ℝ) j151.tangent (0 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j152,hj152⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/16 : ℝ)=z := ⟨_,rfl⟩
  have j152_value : Bounds (-1/16 : ℝ) j152.value (-1/16 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/16 : ℝ))
  have j152_tangent : Bounds (0 : ℝ) j152.tangent (0 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j153,hj153⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant c=z := ⟨_,rfl⟩
  have j153_value : Bounds (159240713813559/500000000000000 : ℝ) j153.value (318481427627119/1000000000000000 : ℝ) := by
    convert hc using 1 <;> norm_num [← hj153,LReturnJets.constant]
  have j153_tangent : Bounds (0 : ℝ) j153.tangent (0 : ℝ) := by
    simpa only [← hj153,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v512 : ℝ := j115.value*j153.value
  have h512 : Bounds (335519292431/1562500000000 : ℝ) v512 (21473234715597/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v513 : ℝ := j115.tangent*j153.value
  have h513 : Bounds (7318449025793/25000000000000 : ℝ) v513 (29273796103217/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v514 : ℝ := j115.value*j153.tangent
  have h514 : Bounds (0 : ℝ) v514 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v515 : ℝ := v513+v514
  have h515 : Bounds (7318449025793/25000000000000 : ℝ) v515 (29273796103217/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h513 h514) (by norm_num) (by norm_num)
  obtain ⟨j154,hj154⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j115 j153=z := ⟨_,rfl⟩
  have j154_value : Bounds (335519292431/1562500000000 : ℝ) j154.value (21473234715597/100000000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h512
  have j154_tangent : Bounds (7318449025793/25000000000000 : ℝ) j154.tangent (29273796103217/100000000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h515
  obtain ⟨j155,hj155⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant d=z := ⟨_,rfl⟩
  have j155_value : Bounds (-1025232119675749/1000000000000000 : ℝ) j155.value (-256308029918937/250000000000000 : ℝ) := by
    convert hd using 1 <;> norm_num [← hj155,LReturnJets.constant]
  have j155_tangent : Bounds (0 : ℝ) j155.tangent (0 : ℝ) := by
    simpa only [← hj155,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v516 : ℝ := j126.value*j155.value
  have h516 : Bounds (-87116237922639/100000000000000 : ℝ) v516 (-43558118961301/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v517 : ℝ := j126.tangent*j155.value
  have h517 : Bounds (-68557330478537/50000000000000 : ℝ) v517 (-3427866523923/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v518 : ℝ := j126.value*j155.tangent
  have h518 : Bounds (0 : ℝ) v518 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j126_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v519 : ℝ := v517+v518
  have h519 : Bounds (-68557330478537/50000000000000 : ℝ) v519 (-3427866523923/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h517 h518) (by norm_num) (by norm_num)
  obtain ⟨j156,hj156⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j126 j155=z := ⟨_,rfl⟩
  have j156_value : Bounds (-87116237922639/100000000000000 : ℝ) j156.value (-43558118961301/50000000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h516
  have j156_tangent : Bounds (-68557330478537/50000000000000 : ℝ) j156.tangent (-3427866523923/2500000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h519
  let v520 : ℝ := j154.value+j156.value
  have h520 : Bounds (-13128600641411/20000000000000 : ℝ) v520 (-13128600641401/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_value j156_value) (by norm_num) (by norm_num)
  let v521 : ℝ := j154.tangent+j156.tangent
  have h521 : Bounds (-53920432426951/50000000000000 : ℝ) v521 (-107840864853703/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_tangent j156_tangent) (by norm_num) (by norm_num)
  obtain ⟨j157,hj157⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j154 j156=z := ⟨_,rfl⟩
  have j157_value : Bounds (-13128600641411/20000000000000 : ℝ) j157.value (-13128600641401/20000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h520
  have j157_tangent : Bounds (-53920432426951/50000000000000 : ℝ) j157.tangent (-107840864853703/100000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h521
  let v522 : ℝ := j152.value*j157.value
  have h522 : Bounds (4102687700437/100000000000000 : ℝ) v522 (4102687700441/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v523 : ℝ := j152.tangent*j157.value
  have h523 : Bounds (0 : ℝ) v523 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v524 : ℝ := j152.value*j157.tangent
  have h524 : Bounds (1685013513339/25000000000000 : ℝ) v524 (6740054053369/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v525 : ℝ := v523+v524
  have h525 : Bounds (1685013513339/25000000000000 : ℝ) v525 (6740054053369/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h523 h524) (by norm_num) (by norm_num)
  obtain ⟨j158,hj158⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j157=z := ⟨_,rfl⟩
  have j158_value : Bounds (4102687700437/100000000000000 : ℝ) j158.value (4102687700441/100000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h522
  have j158_tangent : Bounds (1685013513339/25000000000000 : ℝ) j158.tangent (6740054053369/100000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h525
  let v526 : ℝ := j151.value*j158.value
  have h526 : Bounds (2796057864493/100000000000000 : ℝ) v526 (2796057864497/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v527 : ℝ := j151.tangent*j158.value
  have h527 : Bounds (0 : ℝ) v527 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v528 : ℝ := j151.value*j158.tangent
  have h528 : Bounds (4593472016159/100000000000000 : ℝ) v528 (4593472016169/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v529 : ℝ := v527+v528
  have h529 : Bounds (4593472016159/100000000000000 : ℝ) v529 (4593472016169/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h527 h528) (by norm_num) (by norm_num)
  obtain ⟨j159,hj159⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j158=z := ⟨_,rfl⟩
  have j159_value : Bounds (2796057864493/100000000000000 : ℝ) j159.value (2796057864497/100000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h526
  have j159_tangent : Bounds (4593472016159/100000000000000 : ℝ) j159.tangent (4593472016169/100000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h529
  let v530 : ℝ := -d
  have h530 : Bounds (256308029918937/250000000000000 : ℝ) v530 (1025232119675749/1000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hd) (by norm_num) (by norm_num)
  let v531 : ℝ := (0 : ℝ)+v530
  have h531 : Bounds (51261605983787/50000000000000 : ℝ) v531 (4100928478703/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (0 : ℝ)) h530) (by norm_num) (by norm_num)
  obtain ⟨j160,hj160⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((0 : ℝ)+(-d))=z := ⟨_,rfl⟩
  have j160_value : Bounds (51261605983787/50000000000000 : ℝ) j160.value (4100928478703/4000000000000 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h531
  have j160_tangent : Bounds (0 : ℝ) j160.tangent (0 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v532 : ℝ := j144.value*j153.value
  have h532 : Bounds (5412414084699/20000000000000 : ℝ) v532 (27062070423507/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v533 : ℝ := j144.tangent*j153.value
  have h533 : Bounds (665527227507/1562500000000 : ℝ) v533 (4259374256049/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v534 : ℝ := j144.value*j153.tangent
  have h534 : Bounds (0 : ℝ) v534 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v535 : ℝ := v533+v534
  have h535 : Bounds (665527227507/1562500000000 : ℝ) v535 (4259374256049/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h533 h534) (by norm_num) (by norm_num)
  obtain ⟨j161,hj161⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j144 j153=z := ⟨_,rfl⟩
  have j161_value : Bounds (5412414084699/20000000000000 : ℝ) j161.value (27062070423507/100000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h532
  have j161_tangent : Bounds (665527227507/1562500000000 : ℝ) j161.tangent (4259374256049/10000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h535
  let v536 : ℝ := j150.value*j155.value
  have h536 : Bounds (-125811125912211/100000000000000 : ℝ) v536 (-15726390739023/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v537 : ℝ := j150.tangent*j155.value
  have h537 : Bounds (-11675320273249/6250000000000 : ℝ) v537 (-186805124371869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v538 : ℝ := j150.value*j155.tangent
  have h538 : Bounds (0 : ℝ) v538 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j150_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v539 : ℝ := v537+v538
  have h539 : Bounds (-11675320273249/6250000000000 : ℝ) v539 (-186805124371869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h537 h538) (by norm_num) (by norm_num)
  obtain ⟨j162,hj162⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j150 j155=z := ⟨_,rfl⟩
  have j162_value : Bounds (-125811125912211/100000000000000 : ℝ) j162.value (-15726390739023/12500000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h536
  have j162_tangent : Bounds (-11675320273249/6250000000000 : ℝ) j162.tangent (-186805124371869/100000000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h539
  let v540 : ℝ := j161.value+j162.value
  have h540 : Bounds (-24687263872179/25000000000000 : ℝ) v540 (-98749055488677/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_value j162_value) (by norm_num) (by norm_num)
  let v541 : ℝ := j161.tangent+j162.tangent
  have h541 : Bounds (-9013211363221/6250000000000 : ℝ) v541 (-144211381811379/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_tangent j162_tangent) (by norm_num) (by norm_num)
  obtain ⟨j163,hj163⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j161 j162=z := ⟨_,rfl⟩
  have j163_value : Bounds (-24687263872179/25000000000000 : ℝ) j163.value (-98749055488677/100000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h540
  have j163_tangent : Bounds (-9013211363221/6250000000000 : ℝ) j163.tangent (-144211381811379/100000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h541
  let v542 : ℝ := j152.value*j163.value
  have h542 : Bounds (3085907984021/50000000000000 : ℝ) v542 (1234363193609/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v543 : ℝ := j152.tangent*j163.value
  have h543 : Bounds (0 : ℝ) v543 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v544 : ℝ := j152.value*j163.tangent
  have h544 : Bounds (9013211363211/100000000000000 : ℝ) v544 (9013211363221/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v545 : ℝ := v543+v544
  have h545 : Bounds (9013211363211/100000000000000 : ℝ) v545 (9013211363221/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h543 h544) (by norm_num) (by norm_num)
  obtain ⟨j164,hj164⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j163=z := ⟨_,rfl⟩
  have j164_value : Bounds (3085907984021/50000000000000 : ℝ) j164.value (1234363193609/20000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h542
  have j164_tangent : Bounds (9013211363211/100000000000000 : ℝ) j164.tangent (9013211363221/100000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h545
  let v546 : ℝ := j160.value*j164.value
  have h546 : Bounds (1581885991791/25000000000000 : ℝ) v546 (98867874487/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v547 : ℝ := j160.tangent*j164.value
  have h547 : Bounds (0 : ℝ) v547 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v548 : ℝ := j160.value*j164.tangent
  have h548 : Bounds (924063379099/10000000000000 : ℝ) v548 (9240633791001/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v549 : ℝ := v547+v548
  have h549 : Bounds (924063379099/10000000000000 : ℝ) v549 (9240633791001/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h547 h548) (by norm_num) (by norm_num)
  obtain ⟨j165,hj165⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j164=z := ⟨_,rfl⟩
  have j165_value : Bounds (1581885991791/25000000000000 : ℝ) j165.value (98867874487/1562500000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h546
  have j165_tangent : Bounds (924063379099/10000000000000 : ℝ) j165.tangent (9240633791001/100000000000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h549
  let v550 : ℝ := j159.value+j165.value
  have h550 : Bounds (9123601831657/100000000000000 : ℝ) v550 (1824720366333/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_value j165_value) (by norm_num) (by norm_num)
  let v551 : ℝ := j159.tangent+j165.tangent
  have h551 : Bounds (13834105807149/100000000000000 : ℝ) v551 (1383410580717/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_tangent j165_tangent) (by norm_num) (by norm_num)
  obtain ⟨j166,hj166⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j159 j165=z := ⟨_,rfl⟩
  have j166_value : Bounds (9123601831657/100000000000000 : ℝ) j166.value (1824720366333/20000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h550
  have j166_tangent : Bounds (13834105807149/100000000000000 : ℝ) j166.tangent (1383410580717/10000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h551
  let v552 : ℝ := j166.value⁻¹
  have h552 : Bounds (274014588331039/25000000000000 : ℝ) v552 (548029176662559/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j166_value (by norm_num)) (by norm_num) (by norm_num)
  let v553 : ℝ := -j166.tangent
  have h553 : Bounds (-1383410580717/10000000000000 : ℝ) v553 (-13834105807149/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j166_tangent) (by norm_num) (by norm_num)
  let v554 : ℝ := j166.value*j166.value
  have h554 : Bounds (416200551913/50000000000000 : ℝ) v554 (208100275957/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j166_value j166_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v555 : ℝ := v554⁻¹
  have h555 : Bounds (6006719569455491/50000000000000 : ℝ) v555 (1501679892367481/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h554 (by norm_num)) (by norm_num) (by norm_num)
  let v556 : ℝ := v553*v555
  have h556 : Bounds (-103871992597557/6250000000000 : ℝ) v556 (-830975940777197/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn h553 h555 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j167,hj167⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j166=z := ⟨_,rfl⟩
  have j167_value : Bounds (274014588331039/25000000000000 : ℝ) j167.value (548029176662559/50000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h552
  have j167_tangent : Bounds (-103871992597557/6250000000000 : ℝ) j167.tangent (-830975940777197/50000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h556
  let v557 : ℝ := j158.value*j151.value
  have h557 : Bounds (2796057864493/100000000000000 : ℝ) v557 (2796057864497/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v558 : ℝ := j158.tangent*j151.value
  have h558 : Bounds (4593472016159/100000000000000 : ℝ) v558 (4593472016169/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v559 : ℝ := j158.value*j151.tangent
  have h559 : Bounds (0 : ℝ) v559 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v560 : ℝ := v558+v559
  have h560 : Bounds (4593472016159/100000000000000 : ℝ) v560 (4593472016169/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h558 h559) (by norm_num) (by norm_num)
  obtain ⟨j168,hj168⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j151=z := ⟨_,rfl⟩
  have j168_value : Bounds (2796057864493/100000000000000 : ℝ) j168.value (2796057864497/100000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h557
  have j168_tangent : Bounds (4593472016159/100000000000000 : ℝ) j168.tangent (4593472016169/100000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h560
  let v561 : ℝ := j167.value*j168.value
  have h561 : Bounds (957700805861/3125000000000 : ℝ) v561 (3830803223453/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v562 : ℝ := j167.tangent*j168.value
  have h562 : Bounds (-2323456814427/5000000000000 : ℝ) v562 (-46469136288291/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v563 : ℝ := j167.value*j168.tangent
  have h563 : Bounds (25173566870359/50000000000000 : ℝ) v563 (50347133740873/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v564 : ℝ := v562+v563
  have h564 : Bounds (1938998726089/50000000000000 : ℝ) v564 (1938998726291/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h562 h563) (by norm_num) (by norm_num)
  obtain ⟨j169,hj169⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j168=z := ⟨_,rfl⟩
  have j169_value : Bounds (957700805861/3125000000000 : ℝ) j169.value (3830803223453/12500000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h561
  have j169_tangent : Bounds (1938998726089/50000000000000 : ℝ) j169.tangent (1938998726291/50000000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h564
  let v565 : ℝ := -j169.value
  have h565 : Bounds (-3830803223453/12500000000000 : ℝ) v565 (-957700805861/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_value) (by norm_num) (by norm_num)
  let v566 : ℝ := j0.value+v565
  have h566 : Bounds (8669196776547/12500000000000 : ℝ) v566 (2167299194139/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h565) (by norm_num) (by norm_num)
  let v567 : ℝ := -j169.tangent
  have h567 : Bounds (-1938998726291/50000000000000 : ℝ) v567 (-1938998726089/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_tangent) (by norm_num) (by norm_num)
  let v568 : ℝ := j0.tangent+v567
  have h568 : Bounds (-1938998726291/50000000000000 : ℝ) v568 (-1938998726089/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h567) (by norm_num) (by norm_num)
  obtain ⟨j170,hj170⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j169=z := ⟨_,rfl⟩
  have j170_value : Bounds (8669196776547/12500000000000 : ℝ) j170.value (2167299194139/3125000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h566
  have j170_tangent : Bounds (-1938998726291/50000000000000 : ℝ) j170.tangent (-1938998726089/50000000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h568
  let v569 : ℝ := j170.value*j115.value
  have h569 : Bounds (23380414809787/50000000000000 : ℝ) v569 (46760829619649/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v570 : ℝ := j170.tangent*j115.value
  have h570 : Bounds (-1307347027207/50000000000000 : ℝ) v570 (-2614694054139/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v571 : ℝ := j170.value*j115.tangent
  have h571 : Bounds (398422446021/625000000000 : ℝ) v571 (63747591363523/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v572 : ℝ := v570+v571
  have h572 : Bounds (30566448654473/50000000000000 : ℝ) v572 (7641612163673/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h570 h571) (by norm_num) (by norm_num)
  obtain ⟨j171,hj171⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j115=z := ⟨_,rfl⟩
  have j171_value : Bounds (23380414809787/50000000000000 : ℝ) j171.value (46760829619649/100000000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h569
  have j171_tangent : Bounds (30566448654473/50000000000000 : ℝ) j171.tangent (7641612163673/12500000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h572
  let v573 : ℝ := j158.value*j160.value
  have h573 : Bounds (2103103603743/50000000000000 : ℝ) v573 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v574 : ℝ := j158.tangent*j160.value
  have h574 : Bounds (6910119903851/100000000000000 : ℝ) v574 (1382023980773/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v575 : ℝ := j158.value*j160.tangent
  have h575 : Bounds (0 : ℝ) v575 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v576 : ℝ := v574+v575
  have h576 : Bounds (6910119903851/100000000000000 : ℝ) v576 (1382023980773/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h574 h575) (by norm_num) (by norm_num)
  obtain ⟨j172,hj172⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j160=z := ⟨_,rfl⟩
  have j172_value : Bounds (2103103603743/50000000000000 : ℝ) j172.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h573
  have j172_tangent : Bounds (6910119903851/100000000000000 : ℝ) j172.tangent (1382023980773/20000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h576
  let v577 : ℝ := j167.value*j172.value
  have h577 : Bounds (46102485455773/100000000000000 : ℝ) v577 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v578 : ℝ := j167.tangent*j172.value
  have h578 : Bounds (-4369071239203/6250000000000 : ℝ) v578 (-6990513982689/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v579 : ℝ := j167.value*j172.tangent
  have h579 : Bounds (37869473215437/50000000000000 : ℝ) v579 (37869473215547/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v580 : ℝ := v578+v579
  have h580 : Bounds (2916903301813/50000000000000 : ℝ) v580 (1458451651051/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h578 h579) (by norm_num) (by norm_num)
  obtain ⟨j173,hj173⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j172=z := ⟨_,rfl⟩
  have j173_value : Bounds (46102485455773/100000000000000 : ℝ) j173.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h577
  have j173_tangent : Bounds (2916903301813/50000000000000 : ℝ) j173.tangent (1458451651051/25000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h580
  let v581 : ℝ := -j173.value
  have h581 : Bounds (-46102485455869/100000000000000 : ℝ) v581 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_value) (by norm_num) (by norm_num)
  let v582 : ℝ := j6.value+v581
  have h582 : Bounds (-46102485455869/100000000000000 : ℝ) v582 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h581) (by norm_num) (by norm_num)
  let v583 : ℝ := -j173.tangent
  have h583 : Bounds (-1458451651051/25000000000000 : ℝ) v583 (-2916903301813/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_tangent) (by norm_num) (by norm_num)
  let v584 : ℝ := j6.tangent+v583
  have h584 : Bounds (-1458451651051/25000000000000 : ℝ) v584 (-2916903301813/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h583) (by norm_num) (by norm_num)
  obtain ⟨j174,hj174⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j173=z := ⟨_,rfl⟩
  have j174_value : Bounds (-46102485455869/100000000000000 : ℝ) j174.value (-46102485455773/100000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h582
  have j174_tangent : Bounds (-1458451651051/25000000000000 : ℝ) j174.tangent (-2916903301813/50000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h584
  let v585 : ℝ := j174.value*j144.value
  have h585 : Bounds (-39174300284981/100000000000000 : ℝ) v585 (-19587150142441/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v586 : ℝ := j174.tangent*j144.value
  have h586 : Bounds (-4957114339017/100000000000000 : ℝ) v586 (-4957114338523/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v587 : ℝ := j174.value*j144.tangent
  have h587 : Bounds (-61657516783211/100000000000000 : ℝ) v587 (-61657516783023/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v588 : ℝ := v586+v587
  have h588 : Bounds (-16653657780557/25000000000000 : ℝ) v588 (-33307315560773/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h586 h587) (by norm_num) (by norm_num)
  obtain ⟨j175,hj175⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j144=z := ⟨_,rfl⟩
  have j175_value : Bounds (-39174300284981/100000000000000 : ℝ) j175.value (-19587150142441/50000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h585
  have j175_tangent : Bounds (-16653657780557/25000000000000 : ℝ) j175.tangent (-33307315560773/50000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h588
  let v589 : ℝ := j171.value+j175.value
  have h589 : Bounds (7586529334593/100000000000000 : ℝ) v589 (7586529334767/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_value j175_value) (by norm_num) (by norm_num)
  let v590 : ℝ := j171.tangent+j175.tangent
  have h590 : Bounds (-2740866906641/50000000000000 : ℝ) v590 (-2740866906081/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_tangent j175_tangent) (by norm_num) (by norm_num)
  obtain ⟨j176,hj176⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j171 j175=z := ⟨_,rfl⟩
  have j176_value : Bounds (7586529334593/100000000000000 : ℝ) j176.value (7586529334767/100000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h589
  have j176_tangent : Bounds (-2740866906641/50000000000000 : ℝ) j176.tangent (-2740866906081/50000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h590
  let v591 : ℝ := j167.value*j159.value
  have h591 : Bounds (957700805861/3125000000000 : ℝ) v591 (3830803223453/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v592 : ℝ := j167.tangent*j159.value
  have h592 : Bounds (-2323456814427/5000000000000 : ℝ) v592 (-46469136288291/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v593 : ℝ := j167.value*j159.tangent
  have h593 : Bounds (25173566870359/50000000000000 : ℝ) v593 (50347133740873/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v594 : ℝ := v592+v593
  have h594 : Bounds (1938998726089/50000000000000 : ℝ) v594 (1938998726291/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h592 h593) (by norm_num) (by norm_num)
  obtain ⟨j177,hj177⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j159=z := ⟨_,rfl⟩
  have j177_value : Bounds (957700805861/3125000000000 : ℝ) j177.value (3830803223453/12500000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h591
  have j177_tangent : Bounds (1938998726089/50000000000000 : ℝ) j177.tangent (1938998726291/50000000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h594
  let v595 : ℝ := -j177.value
  have h595 : Bounds (-3830803223453/12500000000000 : ℝ) v595 (-957700805861/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_value) (by norm_num) (by norm_num)
  let v596 : ℝ := j0.value+v595
  have h596 : Bounds (8669196776547/12500000000000 : ℝ) v596 (2167299194139/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h595) (by norm_num) (by norm_num)
  let v597 : ℝ := -j177.tangent
  have h597 : Bounds (-1938998726291/50000000000000 : ℝ) v597 (-1938998726089/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_tangent) (by norm_num) (by norm_num)
  let v598 : ℝ := j0.tangent+v597
  have h598 : Bounds (-1938998726291/50000000000000 : ℝ) v598 (-1938998726089/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h597) (by norm_num) (by norm_num)
  obtain ⟨j178,hj178⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j177=z := ⟨_,rfl⟩
  have j178_value : Bounds (8669196776547/12500000000000 : ℝ) j178.value (2167299194139/3125000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h596
  have j178_tangent : Bounds (-1938998726291/50000000000000 : ℝ) j178.tangent (-1938998726089/50000000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h598
  let v599 : ℝ := j176.value*j178.value
  have h599 : Bounds (526152925221/10000000000000 : ℝ) v599 (5261529252337/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v600 : ℝ := j176.tangent*j178.value
  have h600 : Bounds (-950444582081/25000000000000 : ℝ) v600 (-1900889163771/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j176_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v601 : ℝ := j176.value*j178.tangent
  have h601 : Bounds (-147102707171/50000000000000 : ℝ) v601 (-9193919197/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v602 : ℝ := v600+v601
  have h602 : Bounds (-2047991871333/50000000000000 : ℝ) v602 (-2047991870923/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h600 h601) (by norm_num) (by norm_num)
  obtain ⟨j179,hj179⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j178=z := ⟨_,rfl⟩
  have j179_value : Bounds (526152925221/10000000000000 : ℝ) j179.value (5261529252337/100000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h599
  have j179_tangent : Bounds (-2047991871333/50000000000000 : ℝ) j179.tangent (-2047991870923/50000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h602
  let v603 : ℝ := j170.value*j126.value
  have h603 : Bounds (2357250560499/4000000000000 : ℝ) v603 (29465632006281/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v604 : ℝ := j170.tangent*j126.value
  have h604 : Bounds (-3295220099517/100000000000000 : ℝ) v604 (-3295220099171/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v605 : ℝ := j170.value*j126.tangent
  have h605 : Bounds (46376774740963/50000000000000 : ℝ) v605 (92753549482127/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v606 : ℝ := v604+v605
  have h606 : Bounds (89458329382409/100000000000000 : ℝ) v606 (22364582345739/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h604 h605) (by norm_num) (by norm_num)
  obtain ⟨j180,hj180⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j126=z := ⟨_,rfl⟩
  have j180_value : Bounds (2357250560499/4000000000000 : ℝ) j180.value (29465632006281/50000000000000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h603
  have j180_tangent : Bounds (89458329382409/100000000000000 : ℝ) j180.tangent (22364582345739/25000000000000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h606
  let v607 : ℝ := j174.value*j150.value
  have h607 : Bounds (-56574559958077/100000000000000 : ℝ) v607 (-56574559957947/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v608 : ℝ := j174.tangent*j150.value
  have h608 : Bounds (-7158942478911/100000000000000 : ℝ) v608 (-7158942478199/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v609 : ℝ := j174.value*j150.tangent
  have h609 : Bounds (-21000562614457/25000000000000 : ℝ) v609 (-84002250457601/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v610 : ℝ := v608+v609
  have h610 : Bounds (-91161192936739/100000000000000 : ℝ) v610 (-455805964679/500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h608 h609) (by norm_num) (by norm_num)
  obtain ⟨j181,hj181⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j150=z := ⟨_,rfl⟩
  have j181_value : Bounds (-56574559958077/100000000000000 : ℝ) j181.value (-56574559957947/100000000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h607
  have j181_tangent : Bounds (-91161192936739/100000000000000 : ℝ) j181.tangent (-455805964679/500000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h610
  let v611 : ℝ := j180.value+j181.value
  have h611 : Bounds (1178352027199/50000000000000 : ℝ) v611 (471340810923/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_value j181_value) (by norm_num) (by norm_num)
  let v612 : ℝ := j180.tangent+j181.tangent
  have h612 : Bounds (-170286355433/10000000000000 : ℝ) v612 (-425715888211/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_tangent j181_tangent) (by norm_num) (by norm_num)
  obtain ⟨j182,hj182⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j180 j181=z := ⟨_,rfl⟩
  have j182_value : Bounds (1178352027199/50000000000000 : ℝ) j182.value (471340810923/20000000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h611
  have j182_tangent : Bounds (-170286355433/10000000000000 : ℝ) j182.tangent (-425715888211/25000000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h612
  let v613 : ℝ := j160.value*j158.value
  have h613 : Bounds (2103103603743/50000000000000 : ℝ) v613 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v614 : ℝ := j160.tangent*j158.value
  have h614 : Bounds (0 : ℝ) v614 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v615 : ℝ := j160.value*j158.tangent
  have h615 : Bounds (6910119903851/100000000000000 : ℝ) v615 (1382023980773/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v616 : ℝ := v614+v615
  have h616 : Bounds (6910119903851/100000000000000 : ℝ) v616 (1382023980773/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h614 h615) (by norm_num) (by norm_num)
  obtain ⟨j183,hj183⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j158=z := ⟨_,rfl⟩
  have j183_value : Bounds (2103103603743/50000000000000 : ℝ) j183.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h613
  have j183_tangent : Bounds (6910119903851/100000000000000 : ℝ) j183.tangent (1382023980773/20000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h616
  let v617 : ℝ := j167.value*j183.value
  have h617 : Bounds (46102485455773/100000000000000 : ℝ) v617 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v618 : ℝ := j167.tangent*j183.value
  have h618 : Bounds (-4369071239203/6250000000000 : ℝ) v618 (-6990513982689/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v619 : ℝ := j167.value*j183.tangent
  have h619 : Bounds (37869473215437/50000000000000 : ℝ) v619 (37869473215547/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v620 : ℝ := v618+v619
  have h620 : Bounds (2916903301813/50000000000000 : ℝ) v620 (1458451651051/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h618 h619) (by norm_num) (by norm_num)
  obtain ⟨j184,hj184⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j183=z := ⟨_,rfl⟩
  have j184_value : Bounds (46102485455773/100000000000000 : ℝ) j184.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h617
  have j184_tangent : Bounds (2916903301813/50000000000000 : ℝ) j184.tangent (1458451651051/25000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h620
  let v621 : ℝ := -j184.value
  have h621 : Bounds (-46102485455869/100000000000000 : ℝ) v621 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_value) (by norm_num) (by norm_num)
  let v622 : ℝ := j6.value+v621
  have h622 : Bounds (-46102485455869/100000000000000 : ℝ) v622 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h621) (by norm_num) (by norm_num)
  let v623 : ℝ := -j184.tangent
  have h623 : Bounds (-1458451651051/25000000000000 : ℝ) v623 (-2916903301813/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_tangent) (by norm_num) (by norm_num)
  let v624 : ℝ := j6.tangent+v623
  have h624 : Bounds (-1458451651051/25000000000000 : ℝ) v624 (-2916903301813/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h623) (by norm_num) (by norm_num)
  obtain ⟨j185,hj185⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j184=z := ⟨_,rfl⟩
  have j185_value : Bounds (-46102485455869/100000000000000 : ℝ) j185.value (-46102485455773/100000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h622
  have j185_tangent : Bounds (-1458451651051/25000000000000 : ℝ) j185.tangent (-2916903301813/50000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h624
  let v625 : ℝ := j182.value*j185.value
  have h625 : Bounds (-1086499144017/100000000000000 : ℝ) v625 (-543249571957/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v626 : ℝ := j182.tangent*j185.value
  have h626 : Bounds (785062421781/100000000000000 : ℝ) v626 (785062422469/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j182_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v627 : ℝ := j182.value*j185.tangent
  have h627 : Bounds (-6874277839/5000000000000 : ℝ) v627 (-137485556753/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v628 : ℝ := v626+v627
  have h628 : Bounds (647576865001/100000000000000 : ℝ) v628 (161894216429/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h626 h627) (by norm_num) (by norm_num)
  obtain ⟨j186,hj186⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j185=z := ⟨_,rfl⟩
  have j186_value : Bounds (-1086499144017/100000000000000 : ℝ) j186.value (-543249571957/50000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h625
  have j186_tangent : Bounds (647576865001/100000000000000 : ℝ) j186.tangent (161894216429/25000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h628
  let v629 : ℝ := j179.value+j186.value
  have h629 : Bounds (4175030108193/100000000000000 : ℝ) v629 (4175030108423/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_value j186_value) (by norm_num) (by norm_num)
  let v630 : ℝ := j179.tangent+j186.tangent
  have h630 : Bounds (-689681375533/20000000000000 : ℝ) v630 (-344840687613/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_tangent j186_tangent) (by norm_num) (by norm_num)
  obtain ⟨j187,hj187⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j179 j186=z := ⟨_,rfl⟩
  have j187_value : Bounds (4175030108193/100000000000000 : ℝ) j187.value (4175030108423/100000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h629
  have j187_tangent : Bounds (-689681375533/20000000000000 : ℝ) j187.tangent (-344840687613/10000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h630
  let v631 : ℝ := j158.value*j158.value
  have h631 : Bounds (168320463673/100000000000000 : ℝ) v631 (84160231837/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v632 : ℝ := j158.tangent*j158.value
  have h632 : Bounds (276523368649/100000000000000 : ℝ) v632 (276523368651/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v633 : ℝ := j158.value*j158.tangent
  have h633 : Bounds (276523368649/100000000000000 : ℝ) v633 (276523368651/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v634 : ℝ := v632+v633
  have h634 : Bounds (276523368649/50000000000000 : ℝ) v634 (276523368651/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h632 h633) (by norm_num) (by norm_num)
  obtain ⟨j188,hj188⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j158=z := ⟨_,rfl⟩
  have j188_value : Bounds (168320463673/100000000000000 : ℝ) j188.value (84160231837/50000000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h631
  have j188_tangent : Bounds (276523368649/50000000000000 : ℝ) j188.tangent (276523368651/50000000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h634
  let v635 : ℝ := j167.value*j188.value
  have h635 : Bounds (1844890502441/100000000000000 : ℝ) v635 (368978100491/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v636 : ℝ := j167.tangent*j188.value
  have h636 : Bounds (-2797405113083/100000000000000 : ℝ) v636 (-1398702556527/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v637 : ℝ := j167.value*j188.tangent
  have h637 : Bounds (6061714961941/100000000000000 : ℝ) v637 (6061714961991/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v638 : ℝ := v636+v637
  have h638 : Bounds (1632154924429/50000000000000 : ℝ) v638 (3264309848937/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h636 h637) (by norm_num) (by norm_num)
  obtain ⟨j189,hj189⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j188=z := ⟨_,rfl⟩
  have j189_value : Bounds (1844890502441/100000000000000 : ℝ) j189.value (368978100491/20000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h635
  have j189_tangent : Bounds (1632154924429/50000000000000 : ℝ) j189.tangent (3264309848937/100000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h638
  let v639 : ℝ := j187.value+j189.value
  have h639 : Bounds (3009960305317/50000000000000 : ℝ) v639 (3009960305439/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_value j189_value) (by norm_num) (by norm_num)
  let v640 : ℝ := j187.tangent+j189.tangent
  have h640 : Bounds (-184097028807/100000000000000 : ℝ) v640 (-184097027193/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_tangent j189_tangent) (by norm_num) (by norm_num)
  obtain ⟨j190,hj190⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j187 j189=z := ⟨_,rfl⟩
  have j190_value : Bounds (3009960305317/50000000000000 : ℝ) j190.value (3009960305439/50000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h639
  have j190_tangent : Bounds (-184097028807/100000000000000 : ℝ) j190.tangent (-184097027193/100000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h640
  let v641 : ℝ := j151.value*j164.value
  have h641 : Bounds (65721987617/1562500000000 : ℝ) v641 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v642 : ℝ := j151.tangent*j164.value
  have h642 : Bounds (0 : ℝ) v642 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v643 : ℝ := j151.value*j164.tangent
  have h643 : Bounds (24570683763/400000000000 : ℝ) v643 (3071335470379/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v644 : ℝ := v642+v643
  have h644 : Bounds (24570683763/400000000000 : ℝ) v644 (3071335470379/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h642 h643) (by norm_num) (by norm_num)
  obtain ⟨j191,hj191⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j164=z := ⟨_,rfl⟩
  have j191_value : Bounds (65721987617/1562500000000 : ℝ) j191.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h641
  have j191_tangent : Bounds (24570683763/400000000000 : ℝ) j191.tangent (3071335470379/50000000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h644
  let v645 : ℝ := j167.value*j191.value
  have h645 : Bounds (23051242727897/50000000000000 : ℝ) v645 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v646 : ℝ := j167.tangent*j191.value
  have h646 : Bounds (-4369071239203/6250000000000 : ℝ) v646 (-69905139826923/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v647 : ℝ := j167.value*j191.tangent
  have h647 : Bounds (13465451592661/20000000000000 : ℝ) v647 (67327257963453/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v648 : ℝ := v646+v647
  have h648 : Bounds (-2577881863943/100000000000000 : ℝ) v648 (-257788186347/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h646 h647) (by norm_num) (by norm_num)
  obtain ⟨j192,hj192⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j191=z := ⟨_,rfl⟩
  have j192_value : Bounds (23051242727897/50000000000000 : ℝ) j192.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h645
  have j192_tangent : Bounds (-2577881863943/100000000000000 : ℝ) j192.tangent (-257788186347/10000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h648
  let v649 : ℝ := -j192.value
  have h649 : Bounds (-46102485455869/100000000000000 : ℝ) v649 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_value) (by norm_num) (by norm_num)
  let v650 : ℝ := j6.value+v649
  have h650 : Bounds (-46102485455869/100000000000000 : ℝ) v650 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h649) (by norm_num) (by norm_num)
  let v651 : ℝ := -j192.tangent
  have h651 : Bounds (257788186347/10000000000000 : ℝ) v651 (2577881863943/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_tangent) (by norm_num) (by norm_num)
  let v652 : ℝ := j6.tangent+v651
  have h652 : Bounds (257788186347/10000000000000 : ℝ) v652 (2577881863943/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h651) (by norm_num) (by norm_num)
  obtain ⟨j193,hj193⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j192=z := ⟨_,rfl⟩
  have j193_value : Bounds (-46102485455869/100000000000000 : ℝ) j193.value (-23051242727897/50000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h650
  have j193_tangent : Bounds (257788186347/10000000000000 : ℝ) j193.tangent (2577881863943/100000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h652
  let v653 : ℝ := j176.value*j193.value
  have h653 : Bounds (-3497578583167/100000000000000 : ℝ) v653 (-87439464577/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v654 : ℝ := j176.tangent*j193.value
  have h654 : Bounds (2527215533477/100000000000000 : ℝ) v654 (1263607766999/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j176_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v655 : ℝ := j176.value*j193.tangent
  have h655 : Bounds (195571763783/100000000000000 : ℝ) v655 (12223235239/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v656 : ℝ := v654+v655
  have h656 : Bounds (136139364863/5000000000000 : ℝ) v656 (1361393648911/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h654 h655) (by norm_num) (by norm_num)
  obtain ⟨j194,hj194⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j193=z := ⟨_,rfl⟩
  have j194_value : Bounds (-3497578583167/100000000000000 : ℝ) j194.value (-87439464577/2500000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h653
  have j194_tangent : Bounds (136139364863/5000000000000 : ℝ) j194.tangent (1361393648911/50000000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h656
  let v657 : ℝ := j167.value*j165.value
  have h657 : Bounds (69353574212359/100000000000000 : ℝ) v657 (13870714842493/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v658 : ℝ := j167.tangent*j165.value
  have h658 : Bounds (-105160736018943/100000000000000 : ℝ) v658 (-105160736018463/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v659 : ℝ := j167.value*j165.tangent
  have h659 : Bounds (633017116039/625000000000 : ℝ) v659 (2025654771329/2000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v660 : ℝ := v658+v659
  have h660 : Bounds (-3877997452703/100000000000000 : ℝ) v660 (-3877997452013/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h658 h659) (by norm_num) (by norm_num)
  obtain ⟨j195,hj195⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j165=z := ⟨_,rfl⟩
  have j195_value : Bounds (69353574212359/100000000000000 : ℝ) j195.value (13870714842493/20000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h657
  have j195_tangent : Bounds (-3877997452703/100000000000000 : ℝ) j195.tangent (-3877997452013/100000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h660
  let v661 : ℝ := -j195.value
  have h661 : Bounds (-13870714842493/20000000000000 : ℝ) v661 (-69353574212359/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_value) (by norm_num) (by norm_num)
  let v662 : ℝ := j0.value+v661
  have h662 : Bounds (6129285157507/20000000000000 : ℝ) v662 (30646425787641/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h661) (by norm_num) (by norm_num)
  let v663 : ℝ := -j195.tangent
  have h663 : Bounds (3877997452013/100000000000000 : ℝ) v663 (3877997452703/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_tangent) (by norm_num) (by norm_num)
  let v664 : ℝ := j0.tangent+v663
  have h664 : Bounds (3877997452013/100000000000000 : ℝ) v664 (3877997452703/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h663) (by norm_num) (by norm_num)
  obtain ⟨j196,hj196⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j195=z := ⟨_,rfl⟩
  have j196_value : Bounds (6129285157507/20000000000000 : ℝ) j196.value (30646425787641/100000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h662
  have j196_tangent : Bounds (3877997452013/100000000000000 : ℝ) j196.tangent (3877997452703/100000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h664
  let v665 : ℝ := j182.value*j196.value
  have h665 : Bounds (361122779531/50000000000000 : ℝ) v665 (180561389783/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v666 : ℝ := j182.tangent*j196.value
  have h666 : Bounds (-521866815443/100000000000000 : ℝ) v666 (-104373362997/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j182_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v667 : ℝ := j182.value*j196.tangent
  have h667 : Bounds (91392923181/100000000000000 : ℝ) v667 (45696461603/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v668 : ℝ := v666+v667
  have h668 : Bounds (-215236946131/50000000000000 : ℝ) v668 (-430473891779/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h666 h667) (by norm_num) (by norm_num)
  obtain ⟨j197,hj197⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j196=z := ⟨_,rfl⟩
  have j197_value : Bounds (361122779531/50000000000000 : ℝ) j197.value (180561389783/25000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h665
  have j197_tangent : Bounds (-215236946131/50000000000000 : ℝ) j197.tangent (-430473891779/100000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h668
  let v669 : ℝ := j194.value+j197.value
  have h669 : Bounds (-555066604821/20000000000000 : ℝ) v669 (-693833255987/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_value j197_value) (by norm_num) (by norm_num)
  let v670 : ℝ := j194.tangent+j197.tangent
  have h670 : Bounds (1146156702499/50000000000000 : ℝ) v670 (2292313406043/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_tangent j197_tangent) (by norm_num) (by norm_num)
  obtain ⟨j198,hj198⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j194 j197=z := ⟨_,rfl⟩
  have j198_value : Bounds (-555066604821/20000000000000 : ℝ) j198.value (-693833255987/25000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h669
  have j198_tangent : Bounds (1146156702499/50000000000000 : ℝ) j198.tangent (2292313406043/100000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h670
  let v671 : ℝ := j158.value*j164.value
  have h671 : Bounds (126605167307/50000000000000 : ℝ) v671 (50642066923/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v672 : ℝ := j158.tangent*j164.value
  have h672 : Bounds (415983732319/100000000000000 : ℝ) v672 (415983732321/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v673 : ℝ := j158.value*j164.tangent
  have h673 : Bounds (92445978503/25000000000000 : ℝ) v673 (184891957007/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v674 : ℝ := v672+v673
  have h674 : Bounds (785767646331/100000000000000 : ℝ) v674 (157153529267/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h672 h673) (by norm_num) (by norm_num)
  obtain ⟨j199,hj199⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j164=z := ⟨_,rfl⟩
  have j199_value : Bounds (126605167307/50000000000000 : ℝ) j199.value (50642066923/20000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h671
  have j199_tangent : Bounds (785767646331/100000000000000 : ℝ) j199.tangent (157153529267/20000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h674
  let v675 : ℝ := j167.value*j199.value
  have h675 : Bounds (173458314001/6250000000000 : ℝ) v675 (2775333024031/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v676 : ℝ := j167.tangent*j199.value
  have h676 : Bounds (-4208233920441/100000000000000 : ℝ) v676 (-4208233920407/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v677 : ℝ := j167.value*j199.tangent
  have h677 : Bounds (8612471925329/100000000000000 : ℝ) v677 (8612471925381/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v678 : ℝ := v676+v677
  have h678 : Bounds (550529750611/12500000000000 : ℝ) v678 (2202119002487/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h676 h677) (by norm_num) (by norm_num)
  obtain ⟨j200,hj200⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j199=z := ⟨_,rfl⟩
  have j200_value : Bounds (173458314001/6250000000000 : ℝ) j200.value (2775333024031/100000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h675
  have j200_tangent : Bounds (550529750611/12500000000000 : ℝ) j200.tangent (2202119002487/50000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h678
  let v679 : ℝ := j198.value+j200.value
  have h679 : Bounds (-89/100000000000000 : ℝ) v679 (83/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_value j200_value) (by norm_num) (by norm_num)
  let v680 : ℝ := j198.tangent+j200.tangent
  have h680 : Bounds (3348275704943/50000000000000 : ℝ) v680 (6696551411017/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_tangent j200_tangent) (by norm_num) (by norm_num)
  obtain ⟨j201,hj201⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j198 j200=z := ⟨_,rfl⟩
  have j201_value : Bounds (-89/100000000000000 : ℝ) j201.value (83/100000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h679
  have j201_tangent : Bounds (3348275704943/50000000000000 : ℝ) j201.tangent (6696551411017/100000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h680
  let v681 : ℝ := j164.value*j151.value
  have h681 : Bounds (65721987617/1562500000000 : ℝ) v681 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v682 : ℝ := j164.tangent*j151.value
  have h682 : Bounds (24570683763/400000000000 : ℝ) v682 (3071335470379/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v683 : ℝ := j164.value*j151.tangent
  have h683 : Bounds (0 : ℝ) v683 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v684 : ℝ := v682+v683
  have h684 : Bounds (24570683763/400000000000 : ℝ) v684 (3071335470379/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h682 h683) (by norm_num) (by norm_num)
  obtain ⟨j202,hj202⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j151=z := ⟨_,rfl⟩
  have j202_value : Bounds (65721987617/1562500000000 : ℝ) j202.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h681
  have j202_tangent : Bounds (24570683763/400000000000 : ℝ) j202.tangent (3071335470379/50000000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h684
  let v685 : ℝ := j167.value*j202.value
  have h685 : Bounds (23051242727897/50000000000000 : ℝ) v685 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v686 : ℝ := j167.tangent*j202.value
  have h686 : Bounds (-4369071239203/6250000000000 : ℝ) v686 (-69905139826923/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v687 : ℝ := j167.value*j202.tangent
  have h687 : Bounds (13465451592661/20000000000000 : ℝ) v687 (67327257963453/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v688 : ℝ := v686+v687
  have h688 : Bounds (-2577881863943/100000000000000 : ℝ) v688 (-257788186347/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h686 h687) (by norm_num) (by norm_num)
  obtain ⟨j203,hj203⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j202=z := ⟨_,rfl⟩
  have j203_value : Bounds (23051242727897/50000000000000 : ℝ) j203.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h685
  have j203_tangent : Bounds (-2577881863943/100000000000000 : ℝ) j203.tangent (-257788186347/10000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h688
  let v689 : ℝ := -j203.value
  have h689 : Bounds (-46102485455869/100000000000000 : ℝ) v689 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_value) (by norm_num) (by norm_num)
  let v690 : ℝ := j6.value+v689
  have h690 : Bounds (-46102485455869/100000000000000 : ℝ) v690 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h689) (by norm_num) (by norm_num)
  let v691 : ℝ := -j203.tangent
  have h691 : Bounds (257788186347/10000000000000 : ℝ) v691 (2577881863943/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_tangent) (by norm_num) (by norm_num)
  let v692 : ℝ := j6.tangent+v691
  have h692 : Bounds (257788186347/10000000000000 : ℝ) v692 (2577881863943/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h691) (by norm_num) (by norm_num)
  obtain ⟨j204,hj204⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j203=z := ⟨_,rfl⟩
  have j204_value : Bounds (-46102485455869/100000000000000 : ℝ) j204.value (-23051242727897/50000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h690
  have j204_tangent : Bounds (257788186347/10000000000000 : ℝ) j204.tangent (2577881863943/100000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h692
  let v693 : ℝ := j204.value*j115.value
  have h693 : Bounds (-31084057194233/100000000000000 : ℝ) v693 (-6216811438833/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v694 : ℝ := j204.tangent*j115.value
  have h694 : Bounds (869053224481/50000000000000 : ℝ) v694 (1738106449283/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v695 : ℝ := j204.value*j115.tangent
  have h695 : Bounds (-42375932849269/100000000000000 : ℝ) v695 (-2648495803071/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v696 : ℝ := v694+v695
  have h696 : Bounds (-40637826400307/100000000000000 : ℝ) v696 (-40637826399853/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h694 h695) (by norm_num) (by norm_num)
  obtain ⟨j205,hj205⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j115=z := ⟨_,rfl⟩
  have j205_value : Bounds (-31084057194233/100000000000000 : ℝ) j205.value (-6216811438833/20000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h693
  have j205_tangent : Bounds (-40637826400307/100000000000000 : ℝ) j205.tangent (-40637826399853/100000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h696
  let v697 : ℝ := j164.value*j160.value
  have h697 : Bounds (1581885991791/25000000000000 : ℝ) v697 (98867874487/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v698 : ℝ := j164.tangent*j160.value
  have h698 : Bounds (924063379099/10000000000000 : ℝ) v698 (9240633791001/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v699 : ℝ := j164.value*j160.tangent
  have h699 : Bounds (0 : ℝ) v699 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v700 : ℝ := v698+v699
  have h700 : Bounds (924063379099/10000000000000 : ℝ) v700 (9240633791001/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h698 h699) (by norm_num) (by norm_num)
  obtain ⟨j206,hj206⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j160=z := ⟨_,rfl⟩
  have j206_value : Bounds (1581885991791/25000000000000 : ℝ) j206.value (98867874487/1562500000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h697
  have j206_tangent : Bounds (924063379099/10000000000000 : ℝ) j206.tangent (9240633791001/100000000000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h700
  let v701 : ℝ := j167.value*j206.value
  have h701 : Bounds (69353574212359/100000000000000 : ℝ) v701 (13870714842493/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v702 : ℝ := j167.tangent*j206.value
  have h702 : Bounds (-105160736018943/100000000000000 : ℝ) v702 (-105160736018463/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v703 : ℝ := j167.value*j206.tangent
  have h703 : Bounds (633017116039/625000000000 : ℝ) v703 (2025654771329/2000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v704 : ℝ := v702+v703
  have h704 : Bounds (-3877997452703/100000000000000 : ℝ) v704 (-3877997452013/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h702 h703) (by norm_num) (by norm_num)
  obtain ⟨j207,hj207⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j206=z := ⟨_,rfl⟩
  have j207_value : Bounds (69353574212359/100000000000000 : ℝ) j207.value (13870714842493/20000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h701
  have j207_tangent : Bounds (-3877997452703/100000000000000 : ℝ) j207.tangent (-3877997452013/100000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h704
  let v705 : ℝ := -j207.value
  have h705 : Bounds (-13870714842493/20000000000000 : ℝ) v705 (-69353574212359/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_value) (by norm_num) (by norm_num)
  let v706 : ℝ := j0.value+v705
  have h706 : Bounds (6129285157507/20000000000000 : ℝ) v706 (30646425787641/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h705) (by norm_num) (by norm_num)
  let v707 : ℝ := -j207.tangent
  have h707 : Bounds (3877997452013/100000000000000 : ℝ) v707 (3877997452703/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_tangent) (by norm_num) (by norm_num)
  let v708 : ℝ := j0.tangent+v707
  have h708 : Bounds (3877997452013/100000000000000 : ℝ) v708 (3877997452703/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h707) (by norm_num) (by norm_num)
  obtain ⟨j208,hj208⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j207=z := ⟨_,rfl⟩
  have j208_value : Bounds (6129285157507/20000000000000 : ℝ) j208.value (30646425787641/100000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h706
  have j208_tangent : Bounds (3877997452013/100000000000000 : ℝ) j208.tangent (3877997452703/100000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h708
  let v709 : ℝ := j208.value*j144.value
  have h709 : Bounds (651023624101/2500000000000 : ℝ) v709 (13020472482071/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v710 : ℝ := j208.tangent*j144.value
  have h710 : Bounds (3295220099031/100000000000000 : ℝ) v710 (164761004981/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v711 : ℝ := j208.value*j144.tangent
  have h711 : Bounds (40986564903259/100000000000000 : ℝ) v711 (40986564903441/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v712 : ℝ := v710+v711
  have h712 : Bounds (4428178500229/10000000000000 : ℝ) v712 (44281785003061/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h710 h711) (by norm_num) (by norm_num)
  obtain ⟨j209,hj209⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j144=z := ⟨_,rfl⟩
  have j209_value : Bounds (651023624101/2500000000000 : ℝ) j209.value (13020472482071/50000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h709
  have j209_tangent : Bounds (4428178500229/10000000000000 : ℝ) j209.tangent (44281785003061/100000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h712
  let v713 : ℝ := j205.value+j209.value
  have h713 : Bounds (-5043112230193/100000000000000 : ℝ) v713 (-5043112230023/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_value j209_value) (by norm_num) (by norm_num)
  let v714 : ℝ := j205.tangent+j209.tangent
  have h714 : Bounds (3643958601983/100000000000000 : ℝ) v714 (455494825401/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_tangent j209_tangent) (by norm_num) (by norm_num)
  obtain ⟨j210,hj210⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j205 j209=z := ⟨_,rfl⟩
  have j210_value : Bounds (-5043112230193/100000000000000 : ℝ) j210.value (-5043112230023/100000000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h713
  have j210_tangent : Bounds (3643958601983/100000000000000 : ℝ) j210.tangent (455494825401/12500000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h714
  let v715 : ℝ := j210.value*j178.value
  have h715 : Bounds (-218598661449/6250000000000 : ℝ) v715 (-1748789291531/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v716 : ℝ := j210.tangent*j178.value
  have h716 : Bounds (1263607766647/50000000000000 : ℝ) v716 (2527215534147/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j210_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v717 : ℝ := j210.value*j178.tangent
  have h717 : Bounds (19557176379/10000000000000 : ℝ) v717 (97785881909/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v718 : ℝ := v716+v717
  have h718 : Bounds (680696824271/25000000000000 : ℝ) v718 (544557459593/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h716 h717) (by norm_num) (by norm_num)
  obtain ⟨j211,hj211⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j178=z := ⟨_,rfl⟩
  have j211_value : Bounds (-218598661449/6250000000000 : ℝ) j211.value (-1748789291531/50000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h715
  have j211_tangent : Bounds (680696824271/25000000000000 : ℝ) j211.tangent (544557459593/20000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h718
  let v719 : ℝ := j204.value*j126.value
  have h719 : Bounds (-39174300284981/100000000000000 : ℝ) v719 (-391743002849/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v720 : ℝ := j204.tangent*j126.value
  have h720 : Bounds (2190483164197/100000000000000 : ℝ) v720 (2190483164601/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v721 : ℝ := j204.value*j126.tangent
  have h721 : Bounds (-3853594798951/6250000000000 : ℝ) v721 (-30828758391523/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v722 : ℝ := v720+v721
  have h722 : Bounds (-59467033619019/100000000000000 : ℝ) v722 (-11893406723689/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h720 h721) (by norm_num) (by norm_num)
  obtain ⟨j212,hj212⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j126=z := ⟨_,rfl⟩
  have j212_value : Bounds (-39174300284981/100000000000000 : ℝ) j212.value (-391743002849/1000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h719
  have j212_tangent : Bounds (-59467033619019/100000000000000 : ℝ) j212.tangent (-11893406723689/20000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h722
  let v723 : ℝ := j208.value*j150.value
  have h723 : Bounds (7521538312189/20000000000000 : ℝ) v723 (9401922890271/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v724 : ℝ := j208.tangent*j150.value
  have h724 : Bounds (4758875735151/100000000000000 : ℝ) v724 (594859467/12500000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v725 : ℝ := j208.value*j150.tangent
  have h725 : Bounds (27920064495269/50000000000000 : ℝ) v725 (55840128990767/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v726 : ℝ := v724+v725
  have h726 : Bounds (60599004725689/100000000000000 : ℝ) v726 (60599004726767/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h724 h725) (by norm_num) (by norm_num)
  obtain ⟨j213,hj213⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j150=z := ⟨_,rfl⟩
  have j213_value : Bounds (7521538312189/20000000000000 : ℝ) j213.value (9401922890271/25000000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h723
  have j213_tangent : Bounds (60599004725689/100000000000000 : ℝ) j213.tangent (60599004726767/100000000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h726
  let v727 : ℝ := j212.value+j213.value
  have h727 : Bounds (-391652181009/25000000000000 : ℝ) v727 (-195826090477/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_value j213_value) (by norm_num) (by norm_num)
  let v728 : ℝ := j212.tangent+j213.tangent
  have h728 : Bounds (113197110667/10000000000000 : ℝ) v728 (565985554161/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_tangent j213_tangent) (by norm_num) (by norm_num)
  obtain ⟨j214,hj214⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j212 j213=z := ⟨_,rfl⟩
  have j214_value : Bounds (-391652181009/25000000000000 : ℝ) j214.value (-195826090477/12500000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h727
  have j214_tangent : Bounds (113197110667/10000000000000 : ℝ) j214.tangent (565985554161/50000000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h728
  let v729 : ℝ := j214.value*j185.value
  have h729 : Bounds (361122779523/50000000000000 : ℝ) v729 (14444911183/2000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v730 : ℝ := j214.tangent*j185.value
  have h730 : Bounds (-521866815579/100000000000000 : ℝ) v730 (-16308337963/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j214_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v731 : ℝ := j214.value*j185.tangent
  have h731 : Bounds (45696461591/50000000000000 : ℝ) v731 (18278584641/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v732 : ℝ := v730+v731
  have h732 : Bounds (-430473892397/100000000000000 : ℝ) v732 (-430473891611/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h730 h731) (by norm_num) (by norm_num)
  obtain ⟨j215,hj215⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j185=z := ⟨_,rfl⟩
  have j215_value : Bounds (361122779523/50000000000000 : ℝ) j215.value (14444911183/2000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h729
  have j215_tangent : Bounds (-430473892397/100000000000000 : ℝ) j215.tangent (-430473891611/100000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h732
  let v733 : ℝ := j211.value+j215.value
  have h733 : Bounds (-1387666512069/50000000000000 : ℝ) v733 (-346916627989/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_value j215_value) (by norm_num) (by norm_num)
  let v734 : ℝ := j211.tangent+j215.tangent
  have h734 : Bounds (2292313404687/100000000000000 : ℝ) v734 (1146156703177/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_tangent j215_tangent) (by norm_num) (by norm_num)
  obtain ⟨j216,hj216⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j211 j215=z := ⟨_,rfl⟩
  have j216_value : Bounds (-1387666512069/50000000000000 : ℝ) j216.value (-346916627989/12500000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h733
  have j216_tangent : Bounds (2292313404687/100000000000000 : ℝ) j216.tangent (1146156703177/50000000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h734
  let v735 : ℝ := j164.value*j158.value
  have h735 : Bounds (126605167307/50000000000000 : ℝ) v735 (50642066923/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v736 : ℝ := j164.tangent*j158.value
  have h736 : Bounds (92445978503/25000000000000 : ℝ) v736 (184891957007/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v737 : ℝ := j164.value*j158.tangent
  have h737 : Bounds (415983732319/100000000000000 : ℝ) v737 (415983732321/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v738 : ℝ := v736+v737
  have h738 : Bounds (785767646331/100000000000000 : ℝ) v738 (157153529267/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h736 h737) (by norm_num) (by norm_num)
  obtain ⟨j217,hj217⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j158=z := ⟨_,rfl⟩
  have j217_value : Bounds (126605167307/50000000000000 : ℝ) j217.value (50642066923/20000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h735
  have j217_tangent : Bounds (785767646331/100000000000000 : ℝ) j217.tangent (157153529267/20000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h738
  let v739 : ℝ := j167.value*j217.value
  have h739 : Bounds (173458314001/6250000000000 : ℝ) v739 (2775333024031/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v740 : ℝ := j167.tangent*j217.value
  have h740 : Bounds (-4208233920441/100000000000000 : ℝ) v740 (-4208233920407/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v741 : ℝ := j167.value*j217.tangent
  have h741 : Bounds (8612471925329/100000000000000 : ℝ) v741 (8612471925381/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v742 : ℝ := v740+v741
  have h742 : Bounds (550529750611/12500000000000 : ℝ) v742 (2202119002487/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h740 h741) (by norm_num) (by norm_num)
  obtain ⟨j218,hj218⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j217=z := ⟨_,rfl⟩
  have j218_value : Bounds (173458314001/6250000000000 : ℝ) j218.value (2775333024031/100000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h739
  have j218_tangent : Bounds (550529750611/12500000000000 : ℝ) j218.tangent (2202119002487/50000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h742
  let v743 : ℝ := j216.value+j218.value
  have h743 : Bounds (-61/50000000000000 : ℝ) v743 (119/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_value j218_value) (by norm_num) (by norm_num)
  let v744 : ℝ := j216.tangent+j218.tangent
  have h744 : Bounds (267862056383/4000000000000 : ℝ) v744 (52316807901/781250000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_tangent j218_tangent) (by norm_num) (by norm_num)
  obtain ⟨j219,hj219⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j216 j218=z := ⟨_,rfl⟩
  have j219_value : Bounds (-61/50000000000000 : ℝ) j219.value (119/100000000000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h743
  have j219_tangent : Bounds (267862056383/4000000000000 : ℝ) j219.tangent (52316807901/781250000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h744
  let v745 : ℝ := j210.value*j193.value
  have h745 : Bounds (465000016473/20000000000000 : ℝ) v745 (145312505153/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v746 : ℝ := j210.tangent*j193.value
  have h746 : Bounds (-839977742531/50000000000000 : ℝ) v746 (-839977742247/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j210_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v747 : ℝ := j210.value*j193.tangent
  have h747 : Bounds (-130005475561/100000000000000 : ℝ) v747 (-32501368883/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v748 : ℝ := v746+v747
  have h748 : Bounds (-1809960960623/100000000000000 : ℝ) v748 (-904980480013/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h746 h747) (by norm_num) (by norm_num)
  obtain ⟨j220,hj220⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j193=z := ⟨_,rfl⟩
  have j220_value : Bounds (465000016473/20000000000000 : ℝ) j220.value (145312505153/6250000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h745
  have j220_tangent : Bounds (-1809960960623/100000000000000 : ℝ) j220.tangent (-904980480013/50000000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h748
  let v749 : ℝ := j214.value*j196.value
  have h749 : Bounds (-96021915999/20000000000000 : ℝ) v749 (-19204383197/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v750 : ℝ := j214.tangent*j196.value
  have h750 : Bounds (346908685141/100000000000000 : ℝ) v750 (6938173713/2000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j214_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v751 : ℝ := j214.value*j196.tangent
  have h751 : Bounds (-15188261603/25000000000000 : ℝ) v751 (-7594130799/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v752 : ℝ := v750+v751
  have h752 : Bounds (286155638729/100000000000000 : ℝ) v752 (143077819629/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h750 h751) (by norm_num) (by norm_num)
  obtain ⟨j221,hj221⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j196=z := ⟨_,rfl⟩
  have j221_value : Bounds (-96021915999/20000000000000 : ℝ) j221.value (-19204383197/4000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h749
  have j221_tangent : Bounds (286155638729/100000000000000 : ℝ) j221.tangent (143077819629/50000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h752
  let v753 : ℝ := j220.value+j221.value
  have h753 : Bounds (184489050237/10000000000000 : ℝ) v753 (1844890502523/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_value j221_value) (by norm_num) (by norm_num)
  let v754 : ℝ := j220.tangent+j221.tangent
  have h754 : Bounds (-761902660947/50000000000000 : ℝ) v754 (-23809458137/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_tangent j221_tangent) (by norm_num) (by norm_num)
  obtain ⟨j222,hj222⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j220 j221=z := ⟨_,rfl⟩
  have j222_value : Bounds (184489050237/10000000000000 : ℝ) j222.value (1844890502523/100000000000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h753
  have j222_tangent : Bounds (-761902660947/50000000000000 : ℝ) j222.tangent (-23809458137/1562500000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h754
  let v755 : ℝ := j164.value*j164.value
  have h755 : Bounds (380913123433/100000000000000 : ℝ) v755 (76182624687/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v756 : ℝ := j164.tangent*j164.value
  have h756 : Bounds (139069704537/25000000000000 : ℝ) v756 (556278818149/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v757 : ℝ := j164.value*j164.tangent
  have h757 : Bounds (139069704537/25000000000000 : ℝ) v757 (556278818149/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v758 : ℝ := v756+v757
  have h758 : Bounds (139069704537/12500000000000 : ℝ) v758 (556278818149/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h756 h757) (by norm_num) (by norm_num)
  obtain ⟨j223,hj223⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j164=z := ⟨_,rfl⟩
  have j223_value : Bounds (380913123433/100000000000000 : ℝ) j223.value (76182624687/20000000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h755
  have j223_tangent : Bounds (139069704537/12500000000000 : ℝ) j223.tangent (556278818149/50000000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h758
  let v759 : ℝ := j167.value*j223.value
  have h759 : Bounds (835006021659/20000000000000 : ℝ) v759 (4175030108321/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v760 : ℝ := j167.tangent*j223.value
  have h760 : Bounds (-6330592822041/100000000000000 : ℝ) v760 (-3165296410991/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v761 : ℝ := j167.value*j223.tangent
  have h761 : Bounds (1524285113521/12500000000000 : ℝ) v761 (12194280908201/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v762 : ℝ := v760+v761
  have h762 : Bounds (5863688086127/100000000000000 : ℝ) v762 (5863688086219/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h760 h761) (by norm_num) (by norm_num)
  obtain ⟨j224,hj224⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j223=z := ⟨_,rfl⟩
  have j224_value : Bounds (835006021659/20000000000000 : ℝ) j224.value (4175030108321/100000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h759
  have j224_tangent : Bounds (5863688086127/100000000000000 : ℝ) j224.tangent (5863688086219/100000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h762
  let v763 : ℝ := j222.value+j224.value
  have h763 : Bounds (1203984122133/20000000000000 : ℝ) v763 (1504980152711/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_value j224_value) (by norm_num) (by norm_num)
  let v764 : ℝ := j222.tangent+j224.tangent
  have h764 : Bounds (4339882764233/100000000000000 : ℝ) v764 (4339882765451/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_tangent j224_tangent) (by norm_num) (by norm_num)
  obtain ⟨j225,hj225⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j222 j224=z := ⟨_,rfl⟩
  have j225_value : Bounds (1203984122133/20000000000000 : ℝ) j225.value (1504980152711/25000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h763
  have j225_tangent : Bounds (4339882764233/100000000000000 : ℝ) j225.tangent (4339882765451/100000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h764
  have hm03 : jetIter c d 0 3=!![j190,j201;j219,j225] := by
    rw [jetIter,hm02]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj80,← hj85,← hj151,← hj152,← hj153,← hj154,← hj155,← hj156,← hj157,← hj158,← hj159,← hj160,← hj161,← hj162,← hj163,← hj164,← hj165,← hj166,← hj167,← hj168,← hj169,← hj170,← hj171,← hj172,← hj173,← hj174,← hj175,← hj176,← hj177,← hj178,← hj179,← hj180,← hj181,← hj182,← hj183,← hj184,← hj185,← hj186,← hj187,← hj188,← hj189,← hj190,← hj191,← hj192,← hj193,← hj194,← hj195,← hj196,← hj197,← hj198,← hj199,← hj200,← hj201,← hj202,← hj203,← hj204,← hj205,← hj206,← hj207,← hj208,← hj209,← hj210,← hj211,← hj212,← hj213,← hj214,← hj215,← hj216,← hj217,← hj218,← hj219,← hj220,← hj221,← hj222,← hj223,← hj224,← hj225]
    all_goals rfl
  let v765 : ℝ := j190.value⁻¹
  have h765 : Bounds (1661151474644033/100000000000000 : ℝ) v765 (415287868677841/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j190_value (by norm_num)) (by norm_num) (by norm_num)
  let v766 : ℝ := -j190.tangent
  have h766 : Bounds (184097027193/100000000000000 : ℝ) v766 (184097028807/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j190_tangent) (by norm_num) (by norm_num)
  let v767 : ℝ := j190.value*j190.value
  have h767 : Bounds (362394441583/100000000000000 : ℝ) v767 (362394441613/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j190_value j190_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v768 : ℝ := v767⁻¹
  have h768 : Bounds (27594242217100481/100000000000000 : ℝ) v768 (3449280277423101/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h767 (by norm_num)) (by norm_num) (by norm_num)
  let v769 : ℝ := v766*v768
  have h769 : Bounds (50800179598117/100000000000000 : ℝ) v769 (10160036009539/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn h766 h768 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j226,hj226⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j190=z := ⟨_,rfl⟩
  have j226_value : Bounds (1661151474644033/100000000000000 : ℝ) j226.value (415287868677841/25000000000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h765
  have j226_tangent : Bounds (50800179598117/100000000000000 : ℝ) j226.tangent (10160036009539/20000000000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h769
  let v770 : ℝ := j201.value*j226.value
  have h770 : Bounds (-1479/100000000000000 : ℝ) v770 (1379/100000000000000 : ℝ) := by
    exact mul_corners j201_value j226_value (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v771 : ℝ := j201.tangent*j226.value
  have h771 : Bounds (111239862495617/100000000000000 : ℝ) v771 (55619931259457/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j201_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v772 : ℝ := j201.value*j226.tangent
  have h772 : Bounds (-23/50000000000000 : ℝ) v772 (43/100000000000000 : ℝ) := by
    exact mul_corners j201_value j226_tangent (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v773 : ℝ := v771+v772
  have h773 : Bounds (111239862495571/100000000000000 : ℝ) v773 (111239862518957/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h771 h772) (by norm_num) (by norm_num)
  obtain ⟨j227,hj227⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j201 j226=z := ⟨_,rfl⟩
  have j227_value : Bounds (-1479/100000000000000 : ℝ) j227.value (1379/100000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h770
  have j227_tangent : Bounds (111239862495571/100000000000000 : ℝ) j227.tangent (111239862518957/100000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h773
  have he00 : jacobian c d 0 0=j227.tangent := by
    simp only [jacobian,shapeJet,hm03,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj227,← hj226]
    rfl
  let v774 : ℝ := j225.value*j226.value
  have h774 : Bounds (99999999996461/100000000000000 : ℝ) v774 (100000000003489/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_value j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v775 : ℝ := j225.tangent*j226.value
  have h775 : Bounds (36046013267939/50000000000000 : ℝ) v775 (36046013279517/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v776 : ℝ := j225.value*j226.tangent
  have h776 : Bounds (3058130481881/100000000000000 : ℝ) v776 (1529065254519/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_value j226_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v777 : ℝ := v775+v776
  have h777 : Bounds (75150157017759/100000000000000 : ℝ) v777 (9393769633509/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h775 h776) (by norm_num) (by norm_num)
  obtain ⟨j228,hj228⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j225 j226=z := ⟨_,rfl⟩
  have j228_value : Bounds (99999999996461/100000000000000 : ℝ) j228.value (100000000003489/100000000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h774
  have j228_tangent : Bounds (75150157017759/100000000000000 : ℝ) j228.tangent (9393769633509/12500000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h777
  have he10 : jacobian c d 1 0=j228.tangent := by
    simp only [jacobian,shapeJet,hm03,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj228,← hj226]
    rfl
  rw [he00,he10]
  exact ⟨enlarge j227_tangent (by norm_num) (by norm_num),
    enlarge j228_tangent (by norm_num) (by norm_num)⟩

theorem column_1_bounds {c d : ℝ}
    (hc : Bounds (318481427627118/10^15) c (318481427627119/10^15))
    (hd : Bounds (-1025232119675749/10^15) d (-1025232119675748/10^15)) :
    Bounds (258388041/400000000 : ℝ) (jacobian c d 0 1) (6459701029/10000000000 : ℝ) ∧
    Bounds (2452568441/5000000000 : ℝ) (jacobian c d 1 1) (490513689/1000000000 : ℝ) := by

  obtain ⟨j0,hj0⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (1 : ℝ)=z := ⟨_,rfl⟩
  have j0_value : Bounds (1 : ℝ) j0.value (1 : ℝ) := by
    simpa only [← hj0,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (1 : ℝ))
  have j0_tangent : Bounds (0 : ℝ) j0.tangent (0 : ℝ) := by
    simpa only [← hj0,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j1,hj1⟩ : ∃ z : LReturnJets.Jet, ⟨(0 : ℝ),(0 : ℝ)⟩=z := ⟨_,rfl⟩
  have j1_value : Bounds (0 : ℝ) j1.value (0 : ℝ) := by
    simpa only [← hj1] using (IntervalBounds.exact (0 : ℝ))
  have j1_tangent : Bounds (0 : ℝ) j1.tangent (0 : ℝ) := by
    simpa only [← hj1] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j2,hj2⟩ : ∃ z : LReturnJets.Jet, ⟨(1 : ℝ),(1 : ℝ)⟩=z := ⟨_,rfl⟩
  have j2_value : Bounds (1 : ℝ) j2.value (1 : ℝ) := by
    simpa only [← hj2] using (IntervalBounds.exact (1 : ℝ))
  have j2_tangent : Bounds (1 : ℝ) j2.tangent (1 : ℝ) := by
    simpa only [← hj2] using (IntervalBounds.exact (1 : ℝ))
  have hm10 : jetIter c d 1 0=!![j0,j1;j1,j2] := by
    simp only [← hj0,← hj1,← hj2]
    rfl
  let v0 : ℝ := -(1 : ℝ)
  have h0 : Bounds (-1 : ℝ) v0 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (1 : ℝ))) (by norm_num) (by norm_num)
  let v1 : ℝ := (-1 : ℝ)+v0
  have h1 : Bounds (-2 : ℝ) v1 (-2 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (-1 : ℝ)) h0) (by norm_num) (by norm_num)
  obtain ⟨j3,hj3⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((-1 : ℝ)+(-(1 : ℝ)))=z := ⟨_,rfl⟩
  have j3_value : Bounds (-2 : ℝ) j3.value (-2 : ℝ) := by
    simpa only [← hj3,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h1
  have j3_tangent : Bounds (0 : ℝ) j3.tangent (0 : ℝ) := by
    simpa only [← hj3,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j4,hj4⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1 : ℝ)=z := ⟨_,rfl⟩
  have j4_value : Bounds (-1 : ℝ) j4.value (-1 : ℝ) := by
    simpa only [← hj4,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1 : ℝ))
  have j4_tangent : Bounds (0 : ℝ) j4.tangent (0 : ℝ) := by
    simpa only [← hj4,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v2 : ℝ := j0.value*j0.value
  have h2 : Bounds (1 : ℝ) v2 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j0_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v3 : ℝ := j0.tangent*j0.value
  have h3 : Bounds (0 : ℝ) v3 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j0_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v4 : ℝ := j0.value*j0.tangent
  have h4 : Bounds (0 : ℝ) v4 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j0_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v5 : ℝ := v3+v4
  have h5 : Bounds (0 : ℝ) v5 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h3 h4) (by norm_num) (by norm_num)
  obtain ⟨j5,hj5⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j0 j0=z := ⟨_,rfl⟩
  have j5_value : Bounds (1 : ℝ) j5.value (1 : ℝ) := by
    simpa only [← hj5,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h2
  have j5_tangent : Bounds (0 : ℝ) j5.tangent (0 : ℝ) := by
    simpa only [← hj5,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h5
  obtain ⟨j6,hj6⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (0 : ℝ)=z := ⟨_,rfl⟩
  have j6_value : Bounds (0 : ℝ) j6.value (0 : ℝ) := by
    simpa only [← hj6,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  have j6_tangent : Bounds (0 : ℝ) j6.tangent (0 : ℝ) := by
    simpa only [← hj6,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v6 : ℝ := j1.value*j6.value
  have h6 : Bounds (0 : ℝ) v6 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v7 : ℝ := j1.tangent*j6.value
  have h7 : Bounds (0 : ℝ) v7 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_tangent j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v8 : ℝ := j1.value*j6.tangent
  have h8 : Bounds (0 : ℝ) v8 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j6_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v9 : ℝ := v7+v8
  have h9 : Bounds (0 : ℝ) v9 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h7 h8) (by norm_num) (by norm_num)
  obtain ⟨j7,hj7⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j1 j6=z := ⟨_,rfl⟩
  have j7_value : Bounds (0 : ℝ) j7.value (0 : ℝ) := by
    simpa only [← hj7,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h6
  have j7_tangent : Bounds (0 : ℝ) j7.tangent (0 : ℝ) := by
    simpa only [← hj7,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h9
  let v10 : ℝ := j5.value+j7.value
  have h10 : Bounds (1 : ℝ) v10 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j5_value j7_value) (by norm_num) (by norm_num)
  let v11 : ℝ := j5.tangent+j7.tangent
  have h11 : Bounds (0 : ℝ) v11 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j5_tangent j7_tangent) (by norm_num) (by norm_num)
  obtain ⟨j8,hj8⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j5 j7=z := ⟨_,rfl⟩
  have j8_value : Bounds (1 : ℝ) j8.value (1 : ℝ) := by
    simpa only [← hj8,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h10
  have j8_tangent : Bounds (0 : ℝ) j8.tangent (0 : ℝ) := by
    simpa only [← hj8,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h11
  let v12 : ℝ := j4.value*j8.value
  have h12 : Bounds (-1 : ℝ) v12 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j8_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v13 : ℝ := j4.tangent*j8.value
  have h13 : Bounds (0 : ℝ) v13 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j4_tangent j8_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v14 : ℝ := j4.value*j8.tangent
  have h14 : Bounds (0 : ℝ) v14 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j8_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v15 : ℝ := v13+v14
  have h15 : Bounds (0 : ℝ) v15 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h13 h14) (by norm_num) (by norm_num)
  obtain ⟨j9,hj9⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j4 j8=z := ⟨_,rfl⟩
  have j9_value : Bounds (-1 : ℝ) j9.value (-1 : ℝ) := by
    simpa only [← hj9,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h12
  have j9_tangent : Bounds (0 : ℝ) j9.tangent (0 : ℝ) := by
    simpa only [← hj9,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h15
  let v16 : ℝ := j3.value*j9.value
  have h16 : Bounds (2 : ℝ) v16 (2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j3_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v17 : ℝ := j3.tangent*j9.value
  have h17 : Bounds (0 : ℝ) v17 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j3_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v18 : ℝ := j3.value*j9.tangent
  have h18 : Bounds (0 : ℝ) v18 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j3_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v19 : ℝ := v17+v18
  have h19 : Bounds (0 : ℝ) v19 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h17 h18) (by norm_num) (by norm_num)
  obtain ⟨j10,hj10⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j3 j9=z := ⟨_,rfl⟩
  have j10_value : Bounds (2 : ℝ) j10.value (2 : ℝ) := by
    simpa only [← hj10,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h16
  have j10_tangent : Bounds (0 : ℝ) j10.tangent (0 : ℝ) := by
    simpa only [← hj10,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h19
  let v20 : ℝ := -(0 : ℝ)
  have h20 : Bounds (0 : ℝ) v20 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (0 : ℝ))) (by norm_num) (by norm_num)
  let v21 : ℝ := (-1/8 : ℝ)+v20
  have h21 : Bounds (-1/8 : ℝ) v21 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (-1/8 : ℝ)) h20) (by norm_num) (by norm_num)
  obtain ⟨j11,hj11⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((-1/8 : ℝ)+(-(0 : ℝ)))=z := ⟨_,rfl⟩
  have j11_value : Bounds (-1/8 : ℝ) j11.value (-1/8 : ℝ) := by
    simpa only [← hj11,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h21
  have j11_tangent : Bounds (0 : ℝ) j11.tangent (0 : ℝ) := by
    simpa only [← hj11,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v22 : ℝ := j1.value*j0.value
  have h22 : Bounds (0 : ℝ) v22 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v23 : ℝ := j1.tangent*j0.value
  have h23 : Bounds (0 : ℝ) v23 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v24 : ℝ := j1.value*j0.tangent
  have h24 : Bounds (0 : ℝ) v24 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j1_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v25 : ℝ := v23+v24
  have h25 : Bounds (0 : ℝ) v25 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h23 h24) (by norm_num) (by norm_num)
  obtain ⟨j12,hj12⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j1 j0=z := ⟨_,rfl⟩
  have j12_value : Bounds (0 : ℝ) j12.value (0 : ℝ) := by
    simpa only [← hj12,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h22
  have j12_tangent : Bounds (0 : ℝ) j12.tangent (0 : ℝ) := by
    simpa only [← hj12,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h25
  let v26 : ℝ := j2.value*j6.value
  have h26 : Bounds (0 : ℝ) v26 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j2_value j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v27 : ℝ := j2.tangent*j6.value
  have h27 : Bounds (0 : ℝ) v27 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j2_tangent j6_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v28 : ℝ := j2.value*j6.tangent
  have h28 : Bounds (0 : ℝ) v28 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j2_value j6_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v29 : ℝ := v27+v28
  have h29 : Bounds (0 : ℝ) v29 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h27 h28) (by norm_num) (by norm_num)
  obtain ⟨j13,hj13⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j2 j6=z := ⟨_,rfl⟩
  have j13_value : Bounds (0 : ℝ) j13.value (0 : ℝ) := by
    simpa only [← hj13,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h26
  have j13_tangent : Bounds (0 : ℝ) j13.tangent (0 : ℝ) := by
    simpa only [← hj13,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h29
  let v30 : ℝ := j12.value+j13.value
  have h30 : Bounds (0 : ℝ) v30 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j12_value j13_value) (by norm_num) (by norm_num)
  let v31 : ℝ := j12.tangent+j13.tangent
  have h31 : Bounds (0 : ℝ) v31 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j12_tangent j13_tangent) (by norm_num) (by norm_num)
  obtain ⟨j14,hj14⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j12 j13=z := ⟨_,rfl⟩
  have j14_value : Bounds (0 : ℝ) j14.value (0 : ℝ) := by
    simpa only [← hj14,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h30
  have j14_tangent : Bounds (0 : ℝ) j14.tangent (0 : ℝ) := by
    simpa only [← hj14,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h31
  let v32 : ℝ := j4.value*j14.value
  have h32 : Bounds (0 : ℝ) v32 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j14_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v33 : ℝ := j4.tangent*j14.value
  have h33 : Bounds (0 : ℝ) v33 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j4_tangent j14_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v34 : ℝ := j4.value*j14.tangent
  have h34 : Bounds (0 : ℝ) v34 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j4_value j14_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v35 : ℝ := v33+v34
  have h35 : Bounds (0 : ℝ) v35 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h33 h34) (by norm_num) (by norm_num)
  obtain ⟨j15,hj15⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j4 j14=z := ⟨_,rfl⟩
  have j15_value : Bounds (0 : ℝ) j15.value (0 : ℝ) := by
    simpa only [← hj15,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h32
  have j15_tangent : Bounds (0 : ℝ) j15.tangent (0 : ℝ) := by
    simpa only [← hj15,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h35
  let v36 : ℝ := j11.value*j15.value
  have h36 : Bounds (0 : ℝ) v36 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j11_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v37 : ℝ := j11.tangent*j15.value
  have h37 : Bounds (0 : ℝ) v37 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j11_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v38 : ℝ := j11.value*j15.tangent
  have h38 : Bounds (0 : ℝ) v38 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j11_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v39 : ℝ := v37+v38
  have h39 : Bounds (0 : ℝ) v39 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h37 h38) (by norm_num) (by norm_num)
  obtain ⟨j16,hj16⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j11 j15=z := ⟨_,rfl⟩
  have j16_value : Bounds (0 : ℝ) j16.value (0 : ℝ) := by
    simpa only [← hj16,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h36
  have j16_tangent : Bounds (0 : ℝ) j16.tangent (0 : ℝ) := by
    simpa only [← hj16,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h39
  let v40 : ℝ := j10.value+j16.value
  have h40 : Bounds (2 : ℝ) v40 (2 : ℝ) := by
    exact enlarge (IntervalBounds.add j10_value j16_value) (by norm_num) (by norm_num)
  let v41 : ℝ := j10.tangent+j16.tangent
  have h41 : Bounds (0 : ℝ) v41 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j10_tangent j16_tangent) (by norm_num) (by norm_num)
  obtain ⟨j17,hj17⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j10 j16=z := ⟨_,rfl⟩
  have j17_value : Bounds (2 : ℝ) j17.value (2 : ℝ) := by
    simpa only [← hj17,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h40
  have j17_tangent : Bounds (0 : ℝ) j17.tangent (0 : ℝ) := by
    simpa only [← hj17,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h41
  let v42 : ℝ := j17.value⁻¹
  have h42 : Bounds (1/2 : ℝ) v42 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j17_value (by norm_num)) (by norm_num) (by norm_num)
  let v43 : ℝ := -j17.tangent
  have h43 : Bounds (0 : ℝ) v43 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j17_tangent) (by norm_num) (by norm_num)
  let v44 : ℝ := j17.value*j17.value
  have h44 : Bounds (4 : ℝ) v44 (4 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j17_value j17_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v45 : ℝ := v44⁻¹
  have h45 : Bounds (1/4 : ℝ) v45 (1/4 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h44 (by norm_num)) (by norm_num) (by norm_num)
  let v46 : ℝ := v43*v45
  have h46 : Bounds (0 : ℝ) v46 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn h43 h45 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j18,hj18⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j17=z := ⟨_,rfl⟩
  have j18_value : Bounds (1/2 : ℝ) j18.value (1/2 : ℝ) := by
    simpa only [← hj18,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h42
  have j18_tangent : Bounds (0 : ℝ) j18.tangent (0 : ℝ) := by
    simpa only [← hj18,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h46
  let v47 : ℝ := j9.value*j3.value
  have h47 : Bounds (2 : ℝ) v47 (2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j9_value j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v48 : ℝ := j9.tangent*j3.value
  have h48 : Bounds (0 : ℝ) v48 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j9_tangent j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v49 : ℝ := j9.value*j3.tangent
  have h49 : Bounds (0 : ℝ) v49 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j3_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v50 : ℝ := v48+v49
  have h50 : Bounds (0 : ℝ) v50 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h48 h49) (by norm_num) (by norm_num)
  obtain ⟨j19,hj19⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j3=z := ⟨_,rfl⟩
  have j19_value : Bounds (2 : ℝ) j19.value (2 : ℝ) := by
    simpa only [← hj19,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h47
  have j19_tangent : Bounds (0 : ℝ) j19.tangent (0 : ℝ) := by
    simpa only [← hj19,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h50
  let v51 : ℝ := j18.value*j19.value
  have h51 : Bounds (1 : ℝ) v51 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j19_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v52 : ℝ := j18.tangent*j19.value
  have h52 : Bounds (0 : ℝ) v52 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j19_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v53 : ℝ := j18.value*j19.tangent
  have h53 : Bounds (0 : ℝ) v53 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j19_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v54 : ℝ := v52+v53
  have h54 : Bounds (0 : ℝ) v54 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h52 h53) (by norm_num) (by norm_num)
  obtain ⟨j20,hj20⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j19=z := ⟨_,rfl⟩
  have j20_value : Bounds (1 : ℝ) j20.value (1 : ℝ) := by
    simpa only [← hj20,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h51
  have j20_tangent : Bounds (0 : ℝ) j20.tangent (0 : ℝ) := by
    simpa only [← hj20,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h54
  let v55 : ℝ := -j20.value
  have h55 : Bounds (-1 : ℝ) v55 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg j20_value) (by norm_num) (by norm_num)
  let v56 : ℝ := j0.value+v55
  have h56 : Bounds (0 : ℝ) v56 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h55) (by norm_num) (by norm_num)
  let v57 : ℝ := -j20.tangent
  have h57 : Bounds (0 : ℝ) v57 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j20_tangent) (by norm_num) (by norm_num)
  let v58 : ℝ := j0.tangent+v57
  have h58 : Bounds (0 : ℝ) v58 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h57) (by norm_num) (by norm_num)
  obtain ⟨j21,hj21⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j20=z := ⟨_,rfl⟩
  have j21_value : Bounds (0 : ℝ) j21.value (0 : ℝ) := by
    simpa only [← hj21,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h56
  have j21_tangent : Bounds (0 : ℝ) j21.tangent (0 : ℝ) := by
    simpa only [← hj21,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h58
  let v59 : ℝ := j21.value*j0.value
  have h59 : Bounds (0 : ℝ) v59 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v60 : ℝ := j21.tangent*j0.value
  have h60 : Bounds (0 : ℝ) v60 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v61 : ℝ := j21.value*j0.tangent
  have h61 : Bounds (0 : ℝ) v61 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v62 : ℝ := v60+v61
  have h62 : Bounds (0 : ℝ) v62 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h60 h61) (by norm_num) (by norm_num)
  obtain ⟨j22,hj22⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j21 j0=z := ⟨_,rfl⟩
  have j22_value : Bounds (0 : ℝ) j22.value (0 : ℝ) := by
    simpa only [← hj22,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h59
  have j22_tangent : Bounds (0 : ℝ) j22.tangent (0 : ℝ) := by
    simpa only [← hj22,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h62
  let v63 : ℝ := j9.value*j11.value
  have h63 : Bounds (1/8 : ℝ) v63 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j9_value j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v64 : ℝ := j9.tangent*j11.value
  have h64 : Bounds (0 : ℝ) v64 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j9_tangent j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v65 : ℝ := j9.value*j11.tangent
  have h65 : Bounds (0 : ℝ) v65 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j11_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v66 : ℝ := v64+v65
  have h66 : Bounds (0 : ℝ) v66 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h64 h65) (by norm_num) (by norm_num)
  obtain ⟨j23,hj23⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j11=z := ⟨_,rfl⟩
  have j23_value : Bounds (1/8 : ℝ) j23.value (1/8 : ℝ) := by
    simpa only [← hj23,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h63
  have j23_tangent : Bounds (0 : ℝ) j23.tangent (0 : ℝ) := by
    simpa only [← hj23,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h66
  let v67 : ℝ := j18.value*j23.value
  have h67 : Bounds (1/16 : ℝ) v67 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j23_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v68 : ℝ := j18.tangent*j23.value
  have h68 : Bounds (0 : ℝ) v68 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j23_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v69 : ℝ := j18.value*j23.tangent
  have h69 : Bounds (0 : ℝ) v69 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j23_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v70 : ℝ := v68+v69
  have h70 : Bounds (0 : ℝ) v70 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h68 h69) (by norm_num) (by norm_num)
  obtain ⟨j24,hj24⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j23=z := ⟨_,rfl⟩
  have j24_value : Bounds (1/16 : ℝ) j24.value (1/16 : ℝ) := by
    simpa only [← hj24,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h67
  have j24_tangent : Bounds (0 : ℝ) j24.tangent (0 : ℝ) := by
    simpa only [← hj24,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h70
  let v71 : ℝ := -j24.value
  have h71 : Bounds (-1/16 : ℝ) v71 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j24_value) (by norm_num) (by norm_num)
  let v72 : ℝ := j6.value+v71
  have h72 : Bounds (-1/16 : ℝ) v72 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h71) (by norm_num) (by norm_num)
  let v73 : ℝ := -j24.tangent
  have h73 : Bounds (0 : ℝ) v73 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j24_tangent) (by norm_num) (by norm_num)
  let v74 : ℝ := j6.tangent+v73
  have h74 : Bounds (0 : ℝ) v74 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h73) (by norm_num) (by norm_num)
  obtain ⟨j25,hj25⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j24=z := ⟨_,rfl⟩
  have j25_value : Bounds (-1/16 : ℝ) j25.value (-1/16 : ℝ) := by
    simpa only [← hj25,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h72
  have j25_tangent : Bounds (0 : ℝ) j25.tangent (0 : ℝ) := by
    simpa only [← hj25,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h74
  let v75 : ℝ := j25.value*j1.value
  have h75 : Bounds (0 : ℝ) v75 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v76 : ℝ := j25.tangent*j1.value
  have h76 : Bounds (0 : ℝ) v76 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j25_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v77 : ℝ := j25.value*j1.tangent
  have h77 : Bounds (0 : ℝ) v77 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v78 : ℝ := v76+v77
  have h78 : Bounds (0 : ℝ) v78 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h76 h77) (by norm_num) (by norm_num)
  obtain ⟨j26,hj26⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j25 j1=z := ⟨_,rfl⟩
  have j26_value : Bounds (0 : ℝ) j26.value (0 : ℝ) := by
    simpa only [← hj26,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h75
  have j26_tangent : Bounds (0 : ℝ) j26.tangent (0 : ℝ) := by
    simpa only [← hj26,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h78
  let v79 : ℝ := j22.value+j26.value
  have h79 : Bounds (0 : ℝ) v79 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j22_value j26_value) (by norm_num) (by norm_num)
  let v80 : ℝ := j22.tangent+j26.tangent
  have h80 : Bounds (0 : ℝ) v80 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j22_tangent j26_tangent) (by norm_num) (by norm_num)
  obtain ⟨j27,hj27⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j22 j26=z := ⟨_,rfl⟩
  have j27_value : Bounds (0 : ℝ) j27.value (0 : ℝ) := by
    simpa only [← hj27,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h79
  have j27_tangent : Bounds (0 : ℝ) j27.tangent (0 : ℝ) := by
    simpa only [← hj27,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h80
  let v81 : ℝ := j18.value*j10.value
  have h81 : Bounds (1 : ℝ) v81 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j10_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v82 : ℝ := j18.tangent*j10.value
  have h82 : Bounds (0 : ℝ) v82 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j10_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v83 : ℝ := j18.value*j10.tangent
  have h83 : Bounds (0 : ℝ) v83 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j10_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v84 : ℝ := v82+v83
  have h84 : Bounds (0 : ℝ) v84 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h82 h83) (by norm_num) (by norm_num)
  obtain ⟨j28,hj28⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j10=z := ⟨_,rfl⟩
  have j28_value : Bounds (1 : ℝ) j28.value (1 : ℝ) := by
    simpa only [← hj28,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h81
  have j28_tangent : Bounds (0 : ℝ) j28.tangent (0 : ℝ) := by
    simpa only [← hj28,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h84
  let v85 : ℝ := -j28.value
  have h85 : Bounds (-1 : ℝ) v85 (-1 : ℝ) := by
    exact enlarge (IntervalBounds.neg j28_value) (by norm_num) (by norm_num)
  let v86 : ℝ := j0.value+v85
  have h86 : Bounds (0 : ℝ) v86 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h85) (by norm_num) (by norm_num)
  let v87 : ℝ := -j28.tangent
  have h87 : Bounds (0 : ℝ) v87 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j28_tangent) (by norm_num) (by norm_num)
  let v88 : ℝ := j0.tangent+v87
  have h88 : Bounds (0 : ℝ) v88 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h87) (by norm_num) (by norm_num)
  obtain ⟨j29,hj29⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j28=z := ⟨_,rfl⟩
  have j29_value : Bounds (0 : ℝ) j29.value (0 : ℝ) := by
    simpa only [← hj29,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h86
  have j29_tangent : Bounds (0 : ℝ) j29.tangent (0 : ℝ) := by
    simpa only [← hj29,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h88
  let v89 : ℝ := j27.value*j29.value
  have h89 : Bounds (0 : ℝ) v89 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_value j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v90 : ℝ := j27.tangent*j29.value
  have h90 : Bounds (0 : ℝ) v90 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_tangent j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v91 : ℝ := j27.value*j29.tangent
  have h91 : Bounds (0 : ℝ) v91 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_value j29_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v92 : ℝ := v90+v91
  have h92 : Bounds (0 : ℝ) v92 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h90 h91) (by norm_num) (by norm_num)
  obtain ⟨j30,hj30⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j27 j29=z := ⟨_,rfl⟩
  have j30_value : Bounds (0 : ℝ) j30.value (0 : ℝ) := by
    simpa only [← hj30,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h89
  have j30_tangent : Bounds (0 : ℝ) j30.tangent (0 : ℝ) := by
    simpa only [← hj30,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h92
  let v93 : ℝ := j21.value*j1.value
  have h93 : Bounds (0 : ℝ) v93 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v94 : ℝ := j21.tangent*j1.value
  have h94 : Bounds (0 : ℝ) v94 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v95 : ℝ := j21.value*j1.tangent
  have h95 : Bounds (0 : ℝ) v95 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j21_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v96 : ℝ := v94+v95
  have h96 : Bounds (0 : ℝ) v96 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h94 h95) (by norm_num) (by norm_num)
  obtain ⟨j31,hj31⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j21 j1=z := ⟨_,rfl⟩
  have j31_value : Bounds (0 : ℝ) j31.value (0 : ℝ) := by
    simpa only [← hj31,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h93
  have j31_tangent : Bounds (0 : ℝ) j31.tangent (0 : ℝ) := by
    simpa only [← hj31,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h96
  let v97 : ℝ := j25.value*j2.value
  have h97 : Bounds (-1/16 : ℝ) v97 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v98 : ℝ := j25.tangent*j2.value
  have h98 : Bounds (0 : ℝ) v98 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j25_tangent j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v99 : ℝ := j25.value*j2.tangent
  have h99 : Bounds (-1/16 : ℝ) v99 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j25_value j2_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v100 : ℝ := v98+v99
  have h100 : Bounds (-1/16 : ℝ) v100 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h98 h99) (by norm_num) (by norm_num)
  obtain ⟨j32,hj32⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j25 j2=z := ⟨_,rfl⟩
  have j32_value : Bounds (-1/16 : ℝ) j32.value (-1/16 : ℝ) := by
    simpa only [← hj32,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h97
  have j32_tangent : Bounds (-1/16 : ℝ) j32.tangent (-1/16 : ℝ) := by
    simpa only [← hj32,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h100
  let v101 : ℝ := j31.value+j32.value
  have h101 : Bounds (-1/16 : ℝ) v101 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j31_value j32_value) (by norm_num) (by norm_num)
  let v102 : ℝ := j31.tangent+j32.tangent
  have h102 : Bounds (-1/16 : ℝ) v102 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j31_tangent j32_tangent) (by norm_num) (by norm_num)
  obtain ⟨j33,hj33⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j31 j32=z := ⟨_,rfl⟩
  have j33_value : Bounds (-1/16 : ℝ) j33.value (-1/16 : ℝ) := by
    simpa only [← hj33,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h101
  have j33_tangent : Bounds (-1/16 : ℝ) j33.tangent (-1/16 : ℝ) := by
    simpa only [← hj33,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h102
  let v103 : ℝ := j11.value*j9.value
  have h103 : Bounds (1/8 : ℝ) v103 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j11_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v104 : ℝ := j11.tangent*j9.value
  have h104 : Bounds (0 : ℝ) v104 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j11_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v105 : ℝ := j11.value*j9.tangent
  have h105 : Bounds (0 : ℝ) v105 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j11_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v106 : ℝ := v104+v105
  have h106 : Bounds (0 : ℝ) v106 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h104 h105) (by norm_num) (by norm_num)
  obtain ⟨j34,hj34⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j11 j9=z := ⟨_,rfl⟩
  have j34_value : Bounds (1/8 : ℝ) j34.value (1/8 : ℝ) := by
    simpa only [← hj34,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h103
  have j34_tangent : Bounds (0 : ℝ) j34.tangent (0 : ℝ) := by
    simpa only [← hj34,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h106
  let v107 : ℝ := j18.value*j34.value
  have h107 : Bounds (1/16 : ℝ) v107 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j34_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v108 : ℝ := j18.tangent*j34.value
  have h108 : Bounds (0 : ℝ) v108 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j34_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v109 : ℝ := j18.value*j34.tangent
  have h109 : Bounds (0 : ℝ) v109 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j34_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v110 : ℝ := v108+v109
  have h110 : Bounds (0 : ℝ) v110 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h108 h109) (by norm_num) (by norm_num)
  obtain ⟨j35,hj35⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j34=z := ⟨_,rfl⟩
  have j35_value : Bounds (1/16 : ℝ) j35.value (1/16 : ℝ) := by
    simpa only [← hj35,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h107
  have j35_tangent : Bounds (0 : ℝ) j35.tangent (0 : ℝ) := by
    simpa only [← hj35,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h110
  let v111 : ℝ := -j35.value
  have h111 : Bounds (-1/16 : ℝ) v111 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.neg j35_value) (by norm_num) (by norm_num)
  let v112 : ℝ := j6.value+v111
  have h112 : Bounds (-1/16 : ℝ) v112 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h111) (by norm_num) (by norm_num)
  let v113 : ℝ := -j35.tangent
  have h113 : Bounds (0 : ℝ) v113 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j35_tangent) (by norm_num) (by norm_num)
  let v114 : ℝ := j6.tangent+v113
  have h114 : Bounds (0 : ℝ) v114 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h113) (by norm_num) (by norm_num)
  obtain ⟨j36,hj36⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j35=z := ⟨_,rfl⟩
  have j36_value : Bounds (-1/16 : ℝ) j36.value (-1/16 : ℝ) := by
    simpa only [← hj36,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h112
  have j36_tangent : Bounds (0 : ℝ) j36.tangent (0 : ℝ) := by
    simpa only [← hj36,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h114
  let v115 : ℝ := j33.value*j36.value
  have h115 : Bounds (1/256 : ℝ) v115 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j33_value j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v116 : ℝ := j33.tangent*j36.value
  have h116 : Bounds (1/256 : ℝ) v116 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j33_tangent j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v117 : ℝ := j33.value*j36.tangent
  have h117 : Bounds (0 : ℝ) v117 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j33_value j36_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v118 : ℝ := v116+v117
  have h118 : Bounds (1/256 : ℝ) v118 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add h116 h117) (by norm_num) (by norm_num)
  obtain ⟨j37,hj37⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j33 j36=z := ⟨_,rfl⟩
  have j37_value : Bounds (1/256 : ℝ) j37.value (1/256 : ℝ) := by
    simpa only [← hj37,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h115
  have j37_tangent : Bounds (1/256 : ℝ) j37.tangent (1/256 : ℝ) := by
    simpa only [← hj37,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h118
  let v119 : ℝ := j30.value+j37.value
  have h119 : Bounds (1/256 : ℝ) v119 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j30_value j37_value) (by norm_num) (by norm_num)
  let v120 : ℝ := j30.tangent+j37.tangent
  have h120 : Bounds (1/256 : ℝ) v120 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j30_tangent j37_tangent) (by norm_num) (by norm_num)
  obtain ⟨j38,hj38⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j30 j37=z := ⟨_,rfl⟩
  have j38_value : Bounds (1/256 : ℝ) j38.value (1/256 : ℝ) := by
    simpa only [← hj38,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h119
  have j38_tangent : Bounds (1/256 : ℝ) j38.tangent (1/256 : ℝ) := by
    simpa only [← hj38,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h120
  let v121 : ℝ := j9.value*j9.value
  have h121 : Bounds (1 : ℝ) v121 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j9_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v122 : ℝ := j9.tangent*j9.value
  have h122 : Bounds (0 : ℝ) v122 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j9_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v123 : ℝ := j9.value*j9.tangent
  have h123 : Bounds (0 : ℝ) v123 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v124 : ℝ := v122+v123
  have h124 : Bounds (0 : ℝ) v124 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h122 h123) (by norm_num) (by norm_num)
  obtain ⟨j39,hj39⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j9=z := ⟨_,rfl⟩
  have j39_value : Bounds (1 : ℝ) j39.value (1 : ℝ) := by
    simpa only [← hj39,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h121
  have j39_tangent : Bounds (0 : ℝ) j39.tangent (0 : ℝ) := by
    simpa only [← hj39,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h124
  let v125 : ℝ := j18.value*j39.value
  have h125 : Bounds (1/2 : ℝ) v125 (1/2 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j39_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v126 : ℝ := j18.tangent*j39.value
  have h126 : Bounds (0 : ℝ) v126 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j39_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v127 : ℝ := j18.value*j39.tangent
  have h127 : Bounds (0 : ℝ) v127 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j39_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v128 : ℝ := v126+v127
  have h128 : Bounds (0 : ℝ) v128 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h126 h127) (by norm_num) (by norm_num)
  obtain ⟨j40,hj40⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j39=z := ⟨_,rfl⟩
  have j40_value : Bounds (1/2 : ℝ) j40.value (1/2 : ℝ) := by
    simpa only [← hj40,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h125
  have j40_tangent : Bounds (0 : ℝ) j40.tangent (0 : ℝ) := by
    simpa only [← hj40,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h128
  let v129 : ℝ := j38.value+j40.value
  have h129 : Bounds (129/256 : ℝ) v129 (129/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j38_value j40_value) (by norm_num) (by norm_num)
  let v130 : ℝ := j38.tangent+j40.tangent
  have h130 : Bounds (1/256 : ℝ) v130 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j38_tangent j40_tangent) (by norm_num) (by norm_num)
  obtain ⟨j41,hj41⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j38 j40=z := ⟨_,rfl⟩
  have j41_value : Bounds (129/256 : ℝ) j41.value (129/256 : ℝ) := by
    simpa only [← hj41,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h129
  have j41_tangent : Bounds (1/256 : ℝ) j41.tangent (1/256 : ℝ) := by
    simpa only [← hj41,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h130
  let v131 : ℝ := j3.value*j15.value
  have h131 : Bounds (0 : ℝ) v131 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j3_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v132 : ℝ := j3.tangent*j15.value
  have h132 : Bounds (0 : ℝ) v132 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j3_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v133 : ℝ := j3.value*j15.tangent
  have h133 : Bounds (0 : ℝ) v133 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j3_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v134 : ℝ := v132+v133
  have h134 : Bounds (0 : ℝ) v134 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h132 h133) (by norm_num) (by norm_num)
  obtain ⟨j42,hj42⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j3 j15=z := ⟨_,rfl⟩
  have j42_value : Bounds (0 : ℝ) j42.value (0 : ℝ) := by
    simpa only [← hj42,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h131
  have j42_tangent : Bounds (0 : ℝ) j42.tangent (0 : ℝ) := by
    simpa only [← hj42,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h134
  let v135 : ℝ := j18.value*j42.value
  have h135 : Bounds (0 : ℝ) v135 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j42_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v136 : ℝ := j18.tangent*j42.value
  have h136 : Bounds (0 : ℝ) v136 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j42_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v137 : ℝ := j18.value*j42.tangent
  have h137 : Bounds (0 : ℝ) v137 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j42_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v138 : ℝ := v136+v137
  have h138 : Bounds (0 : ℝ) v138 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h136 h137) (by norm_num) (by norm_num)
  obtain ⟨j43,hj43⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j42=z := ⟨_,rfl⟩
  have j43_value : Bounds (0 : ℝ) j43.value (0 : ℝ) := by
    simpa only [← hj43,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h135
  have j43_tangent : Bounds (0 : ℝ) j43.tangent (0 : ℝ) := by
    simpa only [← hj43,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h138
  let v139 : ℝ := -j43.value
  have h139 : Bounds (0 : ℝ) v139 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j43_value) (by norm_num) (by norm_num)
  let v140 : ℝ := j6.value+v139
  have h140 : Bounds (0 : ℝ) v140 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h139) (by norm_num) (by norm_num)
  let v141 : ℝ := -j43.tangent
  have h141 : Bounds (0 : ℝ) v141 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j43_tangent) (by norm_num) (by norm_num)
  let v142 : ℝ := j6.tangent+v141
  have h142 : Bounds (0 : ℝ) v142 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h141) (by norm_num) (by norm_num)
  obtain ⟨j44,hj44⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j43=z := ⟨_,rfl⟩
  have j44_value : Bounds (0 : ℝ) j44.value (0 : ℝ) := by
    simpa only [← hj44,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h140
  have j44_tangent : Bounds (0 : ℝ) j44.tangent (0 : ℝ) := by
    simpa only [← hj44,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h142
  let v143 : ℝ := j27.value*j44.value
  have h143 : Bounds (0 : ℝ) v143 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_value j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v144 : ℝ := j27.tangent*j44.value
  have h144 : Bounds (0 : ℝ) v144 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_tangent j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v145 : ℝ := j27.value*j44.tangent
  have h145 : Bounds (0 : ℝ) v145 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j27_value j44_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v146 : ℝ := v144+v145
  have h146 : Bounds (0 : ℝ) v146 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h144 h145) (by norm_num) (by norm_num)
  obtain ⟨j45,hj45⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j27 j44=z := ⟨_,rfl⟩
  have j45_value : Bounds (0 : ℝ) j45.value (0 : ℝ) := by
    simpa only [← hj45,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h143
  have j45_tangent : Bounds (0 : ℝ) j45.tangent (0 : ℝ) := by
    simpa only [← hj45,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h146
  let v147 : ℝ := j18.value*j16.value
  have h147 : Bounds (0 : ℝ) v147 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j16_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v148 : ℝ := j18.tangent*j16.value
  have h148 : Bounds (0 : ℝ) v148 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j16_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v149 : ℝ := j18.value*j16.tangent
  have h149 : Bounds (0 : ℝ) v149 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j16_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v150 : ℝ := v148+v149
  have h150 : Bounds (0 : ℝ) v150 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h148 h149) (by norm_num) (by norm_num)
  obtain ⟨j46,hj46⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j16=z := ⟨_,rfl⟩
  have j46_value : Bounds (0 : ℝ) j46.value (0 : ℝ) := by
    simpa only [← hj46,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h147
  have j46_tangent : Bounds (0 : ℝ) j46.tangent (0 : ℝ) := by
    simpa only [← hj46,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h150
  let v151 : ℝ := -j46.value
  have h151 : Bounds (0 : ℝ) v151 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j46_value) (by norm_num) (by norm_num)
  let v152 : ℝ := j0.value+v151
  have h152 : Bounds (1 : ℝ) v152 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h151) (by norm_num) (by norm_num)
  let v153 : ℝ := -j46.tangent
  have h153 : Bounds (0 : ℝ) v153 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j46_tangent) (by norm_num) (by norm_num)
  let v154 : ℝ := j0.tangent+v153
  have h154 : Bounds (0 : ℝ) v154 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h153) (by norm_num) (by norm_num)
  obtain ⟨j47,hj47⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j46=z := ⟨_,rfl⟩
  have j47_value : Bounds (1 : ℝ) j47.value (1 : ℝ) := by
    simpa only [← hj47,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h152
  have j47_tangent : Bounds (0 : ℝ) j47.tangent (0 : ℝ) := by
    simpa only [← hj47,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h154
  let v155 : ℝ := j33.value*j47.value
  have h155 : Bounds (-1/16 : ℝ) v155 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j33_value j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v156 : ℝ := j33.tangent*j47.value
  have h156 : Bounds (-1/16 : ℝ) v156 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j33_tangent j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v157 : ℝ := j33.value*j47.tangent
  have h157 : Bounds (0 : ℝ) v157 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j33_value j47_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v158 : ℝ := v156+v157
  have h158 : Bounds (-1/16 : ℝ) v158 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h156 h157) (by norm_num) (by norm_num)
  obtain ⟨j48,hj48⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j33 j47=z := ⟨_,rfl⟩
  have j48_value : Bounds (-1/16 : ℝ) j48.value (-1/16 : ℝ) := by
    simpa only [← hj48,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h155
  have j48_tangent : Bounds (-1/16 : ℝ) j48.tangent (-1/16 : ℝ) := by
    simpa only [← hj48,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h158
  let v159 : ℝ := j45.value+j48.value
  have h159 : Bounds (-1/16 : ℝ) v159 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j45_value j48_value) (by norm_num) (by norm_num)
  let v160 : ℝ := j45.tangent+j48.tangent
  have h160 : Bounds (-1/16 : ℝ) v160 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j45_tangent j48_tangent) (by norm_num) (by norm_num)
  obtain ⟨j49,hj49⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j45 j48=z := ⟨_,rfl⟩
  have j49_value : Bounds (-1/16 : ℝ) j49.value (-1/16 : ℝ) := by
    simpa only [← hj49,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h159
  have j49_tangent : Bounds (-1/16 : ℝ) j49.tangent (-1/16 : ℝ) := by
    simpa only [← hj49,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h160
  let v161 : ℝ := j9.value*j15.value
  have h161 : Bounds (0 : ℝ) v161 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v162 : ℝ := j9.tangent*j15.value
  have h162 : Bounds (0 : ℝ) v162 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j9_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v163 : ℝ := j9.value*j15.tangent
  have h163 : Bounds (0 : ℝ) v163 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j9_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v164 : ℝ := v162+v163
  have h164 : Bounds (0 : ℝ) v164 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h162 h163) (by norm_num) (by norm_num)
  obtain ⟨j50,hj50⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j9 j15=z := ⟨_,rfl⟩
  have j50_value : Bounds (0 : ℝ) j50.value (0 : ℝ) := by
    simpa only [← hj50,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h161
  have j50_tangent : Bounds (0 : ℝ) j50.tangent (0 : ℝ) := by
    simpa only [← hj50,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h164
  let v165 : ℝ := j18.value*j50.value
  have h165 : Bounds (0 : ℝ) v165 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j50_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v166 : ℝ := j18.tangent*j50.value
  have h166 : Bounds (0 : ℝ) v166 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j50_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v167 : ℝ := j18.value*j50.tangent
  have h167 : Bounds (0 : ℝ) v167 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j50_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v168 : ℝ := v166+v167
  have h168 : Bounds (0 : ℝ) v168 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h166 h167) (by norm_num) (by norm_num)
  obtain ⟨j51,hj51⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j50=z := ⟨_,rfl⟩
  have j51_value : Bounds (0 : ℝ) j51.value (0 : ℝ) := by
    simpa only [← hj51,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h165
  have j51_tangent : Bounds (0 : ℝ) j51.tangent (0 : ℝ) := by
    simpa only [← hj51,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h168
  let v169 : ℝ := j49.value+j51.value
  have h169 : Bounds (-1/16 : ℝ) v169 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j49_value j51_value) (by norm_num) (by norm_num)
  let v170 : ℝ := j49.tangent+j51.tangent
  have h170 : Bounds (-1/16 : ℝ) v170 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j49_tangent j51_tangent) (by norm_num) (by norm_num)
  obtain ⟨j52,hj52⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j49 j51=z := ⟨_,rfl⟩
  have j52_value : Bounds (-1/16 : ℝ) j52.value (-1/16 : ℝ) := by
    simpa only [← hj52,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h169
  have j52_tangent : Bounds (-1/16 : ℝ) j52.tangent (-1/16 : ℝ) := by
    simpa only [← hj52,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h170
  let v171 : ℝ := j15.value*j3.value
  have h171 : Bounds (0 : ℝ) v171 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_value j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v172 : ℝ := j15.tangent*j3.value
  have h172 : Bounds (0 : ℝ) v172 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_tangent j3_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v173 : ℝ := j15.value*j3.tangent
  have h173 : Bounds (0 : ℝ) v173 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j3_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v174 : ℝ := v172+v173
  have h174 : Bounds (0 : ℝ) v174 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h172 h173) (by norm_num) (by norm_num)
  obtain ⟨j53,hj53⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j3=z := ⟨_,rfl⟩
  have j53_value : Bounds (0 : ℝ) j53.value (0 : ℝ) := by
    simpa only [← hj53,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h171
  have j53_tangent : Bounds (0 : ℝ) j53.tangent (0 : ℝ) := by
    simpa only [← hj53,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h174
  let v175 : ℝ := j18.value*j53.value
  have h175 : Bounds (0 : ℝ) v175 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j53_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v176 : ℝ := j18.tangent*j53.value
  have h176 : Bounds (0 : ℝ) v176 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j53_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v177 : ℝ := j18.value*j53.tangent
  have h177 : Bounds (0 : ℝ) v177 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j53_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v178 : ℝ := v176+v177
  have h178 : Bounds (0 : ℝ) v178 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h176 h177) (by norm_num) (by norm_num)
  obtain ⟨j54,hj54⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j53=z := ⟨_,rfl⟩
  have j54_value : Bounds (0 : ℝ) j54.value (0 : ℝ) := by
    simpa only [← hj54,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h175
  have j54_tangent : Bounds (0 : ℝ) j54.tangent (0 : ℝ) := by
    simpa only [← hj54,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h178
  let v179 : ℝ := -j54.value
  have h179 : Bounds (0 : ℝ) v179 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j54_value) (by norm_num) (by norm_num)
  let v180 : ℝ := j6.value+v179
  have h180 : Bounds (0 : ℝ) v180 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h179) (by norm_num) (by norm_num)
  let v181 : ℝ := -j54.tangent
  have h181 : Bounds (0 : ℝ) v181 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j54_tangent) (by norm_num) (by norm_num)
  let v182 : ℝ := j6.tangent+v181
  have h182 : Bounds (0 : ℝ) v182 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h181) (by norm_num) (by norm_num)
  obtain ⟨j55,hj55⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j54=z := ⟨_,rfl⟩
  have j55_value : Bounds (0 : ℝ) j55.value (0 : ℝ) := by
    simpa only [← hj55,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h180
  have j55_tangent : Bounds (0 : ℝ) j55.tangent (0 : ℝ) := by
    simpa only [← hj55,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h182
  let v183 : ℝ := j55.value*j0.value
  have h183 : Bounds (0 : ℝ) v183 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v184 : ℝ := j55.tangent*j0.value
  have h184 : Bounds (0 : ℝ) v184 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_tangent j0_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v185 : ℝ := j55.value*j0.tangent
  have h185 : Bounds (0 : ℝ) v185 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j0_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v186 : ℝ := v184+v185
  have h186 : Bounds (0 : ℝ) v186 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h184 h185) (by norm_num) (by norm_num)
  obtain ⟨j56,hj56⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j55 j0=z := ⟨_,rfl⟩
  have j56_value : Bounds (0 : ℝ) j56.value (0 : ℝ) := by
    simpa only [← hj56,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h183
  have j56_tangent : Bounds (0 : ℝ) j56.tangent (0 : ℝ) := by
    simpa only [← hj56,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h186
  let v187 : ℝ := j15.value*j11.value
  have h187 : Bounds (0 : ℝ) v187 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_value j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v188 : ℝ := j15.tangent*j11.value
  have h188 : Bounds (0 : ℝ) v188 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_tangent j11_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v189 : ℝ := j15.value*j11.tangent
  have h189 : Bounds (0 : ℝ) v189 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j11_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v190 : ℝ := v188+v189
  have h190 : Bounds (0 : ℝ) v190 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h188 h189) (by norm_num) (by norm_num)
  obtain ⟨j57,hj57⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j11=z := ⟨_,rfl⟩
  have j57_value : Bounds (0 : ℝ) j57.value (0 : ℝ) := by
    simpa only [← hj57,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h187
  have j57_tangent : Bounds (0 : ℝ) j57.tangent (0 : ℝ) := by
    simpa only [← hj57,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h190
  let v191 : ℝ := j18.value*j57.value
  have h191 : Bounds (0 : ℝ) v191 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j57_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v192 : ℝ := j18.tangent*j57.value
  have h192 : Bounds (0 : ℝ) v192 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j57_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v193 : ℝ := j18.value*j57.tangent
  have h193 : Bounds (0 : ℝ) v193 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j57_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v194 : ℝ := v192+v193
  have h194 : Bounds (0 : ℝ) v194 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h192 h193) (by norm_num) (by norm_num)
  obtain ⟨j58,hj58⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j57=z := ⟨_,rfl⟩
  have j58_value : Bounds (0 : ℝ) j58.value (0 : ℝ) := by
    simpa only [← hj58,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h191
  have j58_tangent : Bounds (0 : ℝ) j58.tangent (0 : ℝ) := by
    simpa only [← hj58,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h194
  let v195 : ℝ := -j58.value
  have h195 : Bounds (0 : ℝ) v195 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j58_value) (by norm_num) (by norm_num)
  let v196 : ℝ := j0.value+v195
  have h196 : Bounds (1 : ℝ) v196 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h195) (by norm_num) (by norm_num)
  let v197 : ℝ := -j58.tangent
  have h197 : Bounds (0 : ℝ) v197 (0 : ℝ) := by
    exact enlarge (IntervalBounds.neg j58_tangent) (by norm_num) (by norm_num)
  let v198 : ℝ := j0.tangent+v197
  have h198 : Bounds (0 : ℝ) v198 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h197) (by norm_num) (by norm_num)
  obtain ⟨j59,hj59⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j58=z := ⟨_,rfl⟩
  have j59_value : Bounds (1 : ℝ) j59.value (1 : ℝ) := by
    simpa only [← hj59,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h196
  have j59_tangent : Bounds (0 : ℝ) j59.tangent (0 : ℝ) := by
    simpa only [← hj59,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h198
  let v199 : ℝ := j59.value*j1.value
  have h199 : Bounds (0 : ℝ) v199 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v200 : ℝ := j59.tangent*j1.value
  have h200 : Bounds (0 : ℝ) v200 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v201 : ℝ := j59.value*j1.tangent
  have h201 : Bounds (0 : ℝ) v201 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v202 : ℝ := v200+v201
  have h202 : Bounds (0 : ℝ) v202 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h200 h201) (by norm_num) (by norm_num)
  obtain ⟨j60,hj60⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j59 j1=z := ⟨_,rfl⟩
  have j60_value : Bounds (0 : ℝ) j60.value (0 : ℝ) := by
    simpa only [← hj60,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h199
  have j60_tangent : Bounds (0 : ℝ) j60.tangent (0 : ℝ) := by
    simpa only [← hj60,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h202
  let v203 : ℝ := j56.value+j60.value
  have h203 : Bounds (0 : ℝ) v203 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j56_value j60_value) (by norm_num) (by norm_num)
  let v204 : ℝ := j56.tangent+j60.tangent
  have h204 : Bounds (0 : ℝ) v204 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add j56_tangent j60_tangent) (by norm_num) (by norm_num)
  obtain ⟨j61,hj61⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j56 j60=z := ⟨_,rfl⟩
  have j61_value : Bounds (0 : ℝ) j61.value (0 : ℝ) := by
    simpa only [← hj61,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h203
  have j61_tangent : Bounds (0 : ℝ) j61.tangent (0 : ℝ) := by
    simpa only [← hj61,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h204
  let v205 : ℝ := j61.value*j29.value
  have h205 : Bounds (0 : ℝ) v205 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_value j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v206 : ℝ := j61.tangent*j29.value
  have h206 : Bounds (0 : ℝ) v206 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_tangent j29_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v207 : ℝ := j61.value*j29.tangent
  have h207 : Bounds (0 : ℝ) v207 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_value j29_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v208 : ℝ := v206+v207
  have h208 : Bounds (0 : ℝ) v208 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h206 h207) (by norm_num) (by norm_num)
  obtain ⟨j62,hj62⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j61 j29=z := ⟨_,rfl⟩
  have j62_value : Bounds (0 : ℝ) j62.value (0 : ℝ) := by
    simpa only [← hj62,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h205
  have j62_tangent : Bounds (0 : ℝ) j62.tangent (0 : ℝ) := by
    simpa only [← hj62,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h208
  let v209 : ℝ := j55.value*j1.value
  have h209 : Bounds (0 : ℝ) v209 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v210 : ℝ := j55.tangent*j1.value
  have h210 : Bounds (0 : ℝ) v210 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_tangent j1_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v211 : ℝ := j55.value*j1.tangent
  have h211 : Bounds (0 : ℝ) v211 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j55_value j1_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v212 : ℝ := v210+v211
  have h212 : Bounds (0 : ℝ) v212 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h210 h211) (by norm_num) (by norm_num)
  obtain ⟨j63,hj63⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j55 j1=z := ⟨_,rfl⟩
  have j63_value : Bounds (0 : ℝ) j63.value (0 : ℝ) := by
    simpa only [← hj63,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h209
  have j63_tangent : Bounds (0 : ℝ) j63.tangent (0 : ℝ) := by
    simpa only [← hj63,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h212
  let v213 : ℝ := j59.value*j2.value
  have h213 : Bounds (1 : ℝ) v213 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v214 : ℝ := j59.tangent*j2.value
  have h214 : Bounds (0 : ℝ) v214 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_tangent j2_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v215 : ℝ := j59.value*j2.tangent
  have h215 : Bounds (1 : ℝ) v215 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j59_value j2_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v216 : ℝ := v214+v215
  have h216 : Bounds (1 : ℝ) v216 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h214 h215) (by norm_num) (by norm_num)
  obtain ⟨j64,hj64⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j59 j2=z := ⟨_,rfl⟩
  have j64_value : Bounds (1 : ℝ) j64.value (1 : ℝ) := by
    simpa only [← hj64,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h213
  have j64_tangent : Bounds (1 : ℝ) j64.tangent (1 : ℝ) := by
    simpa only [← hj64,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h216
  let v217 : ℝ := j63.value+j64.value
  have h217 : Bounds (1 : ℝ) v217 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j63_value j64_value) (by norm_num) (by norm_num)
  let v218 : ℝ := j63.tangent+j64.tangent
  have h218 : Bounds (1 : ℝ) v218 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j63_tangent j64_tangent) (by norm_num) (by norm_num)
  obtain ⟨j65,hj65⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j63 j64=z := ⟨_,rfl⟩
  have j65_value : Bounds (1 : ℝ) j65.value (1 : ℝ) := by
    simpa only [← hj65,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h217
  have j65_tangent : Bounds (1 : ℝ) j65.tangent (1 : ℝ) := by
    simpa only [← hj65,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h218
  let v219 : ℝ := j65.value*j36.value
  have h219 : Bounds (-1/16 : ℝ) v219 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j65_value j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v220 : ℝ := j65.tangent*j36.value
  have h220 : Bounds (-1/16 : ℝ) v220 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j65_tangent j36_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v221 : ℝ := j65.value*j36.tangent
  have h221 : Bounds (0 : ℝ) v221 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j65_value j36_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v222 : ℝ := v220+v221
  have h222 : Bounds (-1/16 : ℝ) v222 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h220 h221) (by norm_num) (by norm_num)
  obtain ⟨j66,hj66⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j65 j36=z := ⟨_,rfl⟩
  have j66_value : Bounds (-1/16 : ℝ) j66.value (-1/16 : ℝ) := by
    simpa only [← hj66,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h219
  have j66_tangent : Bounds (-1/16 : ℝ) j66.tangent (-1/16 : ℝ) := by
    simpa only [← hj66,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h222
  let v223 : ℝ := j62.value+j66.value
  have h223 : Bounds (-1/16 : ℝ) v223 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j62_value j66_value) (by norm_num) (by norm_num)
  let v224 : ℝ := j62.tangent+j66.tangent
  have h224 : Bounds (-1/16 : ℝ) v224 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j62_tangent j66_tangent) (by norm_num) (by norm_num)
  obtain ⟨j67,hj67⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j62 j66=z := ⟨_,rfl⟩
  have j67_value : Bounds (-1/16 : ℝ) j67.value (-1/16 : ℝ) := by
    simpa only [← hj67,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h223
  have j67_tangent : Bounds (-1/16 : ℝ) j67.tangent (-1/16 : ℝ) := by
    simpa only [← hj67,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h224
  let v225 : ℝ := j15.value*j9.value
  have h225 : Bounds (0 : ℝ) v225 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_value j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v226 : ℝ := j15.tangent*j9.value
  have h226 : Bounds (0 : ℝ) v226 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j15_tangent j9_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v227 : ℝ := j15.value*j9.tangent
  have h227 : Bounds (0 : ℝ) v227 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j9_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v228 : ℝ := v226+v227
  have h228 : Bounds (0 : ℝ) v228 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h226 h227) (by norm_num) (by norm_num)
  obtain ⟨j68,hj68⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j9=z := ⟨_,rfl⟩
  have j68_value : Bounds (0 : ℝ) j68.value (0 : ℝ) := by
    simpa only [← hj68,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h225
  have j68_tangent : Bounds (0 : ℝ) j68.tangent (0 : ℝ) := by
    simpa only [← hj68,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h228
  let v229 : ℝ := j18.value*j68.value
  have h229 : Bounds (0 : ℝ) v229 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j68_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v230 : ℝ := j18.tangent*j68.value
  have h230 : Bounds (0 : ℝ) v230 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j68_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v231 : ℝ := j18.value*j68.tangent
  have h231 : Bounds (0 : ℝ) v231 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j68_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v232 : ℝ := v230+v231
  have h232 : Bounds (0 : ℝ) v232 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h230 h231) (by norm_num) (by norm_num)
  obtain ⟨j69,hj69⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j68=z := ⟨_,rfl⟩
  have j69_value : Bounds (0 : ℝ) j69.value (0 : ℝ) := by
    simpa only [← hj69,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h229
  have j69_tangent : Bounds (0 : ℝ) j69.tangent (0 : ℝ) := by
    simpa only [← hj69,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h232
  let v233 : ℝ := j67.value+j69.value
  have h233 : Bounds (-1/16 : ℝ) v233 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j67_value j69_value) (by norm_num) (by norm_num)
  let v234 : ℝ := j67.tangent+j69.tangent
  have h234 : Bounds (-1/16 : ℝ) v234 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j67_tangent j69_tangent) (by norm_num) (by norm_num)
  obtain ⟨j70,hj70⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j67 j69=z := ⟨_,rfl⟩
  have j70_value : Bounds (-1/16 : ℝ) j70.value (-1/16 : ℝ) := by
    simpa only [← hj70,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h233
  have j70_tangent : Bounds (-1/16 : ℝ) j70.tangent (-1/16 : ℝ) := by
    simpa only [← hj70,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h234
  let v235 : ℝ := j61.value*j44.value
  have h235 : Bounds (0 : ℝ) v235 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_value j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v236 : ℝ := j61.tangent*j44.value
  have h236 : Bounds (0 : ℝ) v236 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_tangent j44_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v237 : ℝ := j61.value*j44.tangent
  have h237 : Bounds (0 : ℝ) v237 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j61_value j44_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v238 : ℝ := v236+v237
  have h238 : Bounds (0 : ℝ) v238 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h236 h237) (by norm_num) (by norm_num)
  obtain ⟨j71,hj71⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j61 j44=z := ⟨_,rfl⟩
  have j71_value : Bounds (0 : ℝ) j71.value (0 : ℝ) := by
    simpa only [← hj71,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h235
  have j71_tangent : Bounds (0 : ℝ) j71.tangent (0 : ℝ) := by
    simpa only [← hj71,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h238
  let v239 : ℝ := j65.value*j47.value
  have h239 : Bounds (1 : ℝ) v239 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j65_value j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v240 : ℝ := j65.tangent*j47.value
  have h240 : Bounds (1 : ℝ) v240 (1 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j65_tangent j47_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v241 : ℝ := j65.value*j47.tangent
  have h241 : Bounds (0 : ℝ) v241 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j65_value j47_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v242 : ℝ := v240+v241
  have h242 : Bounds (1 : ℝ) v242 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add h240 h241) (by norm_num) (by norm_num)
  obtain ⟨j72,hj72⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j65 j47=z := ⟨_,rfl⟩
  have j72_value : Bounds (1 : ℝ) j72.value (1 : ℝ) := by
    simpa only [← hj72,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h239
  have j72_tangent : Bounds (1 : ℝ) j72.tangent (1 : ℝ) := by
    simpa only [← hj72,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h242
  let v243 : ℝ := j71.value+j72.value
  have h243 : Bounds (1 : ℝ) v243 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j71_value j72_value) (by norm_num) (by norm_num)
  let v244 : ℝ := j71.tangent+j72.tangent
  have h244 : Bounds (1 : ℝ) v244 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j71_tangent j72_tangent) (by norm_num) (by norm_num)
  obtain ⟨j73,hj73⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j71 j72=z := ⟨_,rfl⟩
  have j73_value : Bounds (1 : ℝ) j73.value (1 : ℝ) := by
    simpa only [← hj73,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h243
  have j73_tangent : Bounds (1 : ℝ) j73.tangent (1 : ℝ) := by
    simpa only [← hj73,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h244
  let v245 : ℝ := j15.value*j15.value
  have h245 : Bounds (0 : ℝ) v245 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v246 : ℝ := j15.tangent*j15.value
  have h246 : Bounds (0 : ℝ) v246 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_tangent j15_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v247 : ℝ := j15.value*j15.tangent
  have h247 : Bounds (0 : ℝ) v247 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j15_value j15_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v248 : ℝ := v246+v247
  have h248 : Bounds (0 : ℝ) v248 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h246 h247) (by norm_num) (by norm_num)
  obtain ⟨j74,hj74⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j15 j15=z := ⟨_,rfl⟩
  have j74_value : Bounds (0 : ℝ) j74.value (0 : ℝ) := by
    simpa only [← hj74,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h245
  have j74_tangent : Bounds (0 : ℝ) j74.tangent (0 : ℝ) := by
    simpa only [← hj74,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h248
  let v249 : ℝ := j18.value*j74.value
  have h249 : Bounds (0 : ℝ) v249 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j74_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v250 : ℝ := j18.tangent*j74.value
  have h250 : Bounds (0 : ℝ) v250 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_tangent j74_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v251 : ℝ := j18.value*j74.tangent
  have h251 : Bounds (0 : ℝ) v251 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j18_value j74_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v252 : ℝ := v250+v251
  have h252 : Bounds (0 : ℝ) v252 (0 : ℝ) := by
    exact enlarge (IntervalBounds.add h250 h251) (by norm_num) (by norm_num)
  obtain ⟨j75,hj75⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j18 j74=z := ⟨_,rfl⟩
  have j75_value : Bounds (0 : ℝ) j75.value (0 : ℝ) := by
    simpa only [← hj75,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h249
  have j75_tangent : Bounds (0 : ℝ) j75.tangent (0 : ℝ) := by
    simpa only [← hj75,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h252
  let v253 : ℝ := j73.value+j75.value
  have h253 : Bounds (1 : ℝ) v253 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j73_value j75_value) (by norm_num) (by norm_num)
  let v254 : ℝ := j73.tangent+j75.tangent
  have h254 : Bounds (1 : ℝ) v254 (1 : ℝ) := by
    exact enlarge (IntervalBounds.add j73_tangent j75_tangent) (by norm_num) (by norm_num)
  obtain ⟨j76,hj76⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j73 j75=z := ⟨_,rfl⟩
  have j76_value : Bounds (1 : ℝ) j76.value (1 : ℝ) := by
    simpa only [← hj76,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h253
  have j76_tangent : Bounds (1 : ℝ) j76.tangent (1 : ℝ) := by
    simpa only [← hj76,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h254
  have hm11 : jetIter c d 1 1=!![j41,j52;j70,j76] := by
    rw [jetIter,hm10]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj5,← hj6,← hj7,← hj8,← hj9,← hj10,← hj11,← hj12,← hj13,← hj14,← hj15,← hj16,← hj17,← hj18,← hj19,← hj20,← hj21,← hj22,← hj23,← hj24,← hj25,← hj26,← hj27,← hj28,← hj29,← hj30,← hj31,← hj32,← hj33,← hj34,← hj35,← hj36,← hj37,← hj38,← hj39,← hj40,← hj41,← hj42,← hj43,← hj44,← hj45,← hj46,← hj47,← hj48,← hj49,← hj50,← hj51,← hj52,← hj53,← hj54,← hj55,← hj56,← hj57,← hj58,← hj59,← hj60,← hj61,← hj62,← hj63,← hj64,← hj65,← hj66,← hj67,← hj68,← hj69,← hj70,← hj71,← hj72,← hj73,← hj74,← hj75,← hj76]
    all_goals rfl
  let v255 : ℝ := -(-1 : ℝ)
  have h255 : Bounds (1 : ℝ) v255 (1 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (-1 : ℝ))) (by norm_num) (by norm_num)
  let v256 : ℝ := c+v255
  have h256 : Bounds (131848142762711/100000000000000 : ℝ) v256 (16481017845339/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hc h255) (by norm_num) (by norm_num)
  obtain ⟨j77,hj77⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (c+(-(-1 : ℝ)))=z := ⟨_,rfl⟩
  have j77_value : Bounds (131848142762711/100000000000000 : ℝ) j77.value (16481017845339/12500000000000 : ℝ) := by
    simpa only [← hj77,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h256
  have j77_tangent : Bounds (0 : ℝ) j77.tangent (0 : ℝ) := by
    simpa only [← hj77,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j78,hj78⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/4 : ℝ)=z := ⟨_,rfl⟩
  have j78_value : Bounds (-1/4 : ℝ) j78.value (-1/4 : ℝ) := by
    simpa only [← hj78,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/4 : ℝ))
  have j78_tangent : Bounds (0 : ℝ) j78.tangent (0 : ℝ) := by
    simpa only [← hj78,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v257 : ℝ := j41.value*j4.value
  have h257 : Bounds (-129/256 : ℝ) v257 (-129/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j41_value j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v258 : ℝ := j41.tangent*j4.value
  have h258 : Bounds (-1/256 : ℝ) v258 (-1/256 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j41_tangent j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v259 : ℝ := j41.value*j4.tangent
  have h259 : Bounds (0 : ℝ) v259 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j41_value j4_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v260 : ℝ := v258+v259
  have h260 : Bounds (-1/256 : ℝ) v260 (-1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add h258 h259) (by norm_num) (by norm_num)
  obtain ⟨j79,hj79⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j41 j4=z := ⟨_,rfl⟩
  have j79_value : Bounds (-129/256 : ℝ) j79.value (-129/256 : ℝ) := by
    simpa only [← hj79,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h257
  have j79_tangent : Bounds (-1/256 : ℝ) j79.tangent (-1/256 : ℝ) := by
    simpa only [← hj79,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h260
  obtain ⟨j80,hj80⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/8 : ℝ)=z := ⟨_,rfl⟩
  have j80_value : Bounds (-1/8 : ℝ) j80.value (-1/8 : ℝ) := by
    simpa only [← hj80,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/8 : ℝ))
  have j80_tangent : Bounds (0 : ℝ) j80.tangent (0 : ℝ) := by
    simpa only [← hj80,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v261 : ℝ := j52.value*j80.value
  have h261 : Bounds (1/128 : ℝ) v261 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j52_value j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v262 : ℝ := j52.tangent*j80.value
  have h262 : Bounds (1/128 : ℝ) v262 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j52_tangent j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v263 : ℝ := j52.value*j80.tangent
  have h263 : Bounds (0 : ℝ) v263 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j52_value j80_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v264 : ℝ := v262+v263
  have h264 : Bounds (1/128 : ℝ) v264 (1/128 : ℝ) := by
    exact enlarge (IntervalBounds.add h262 h263) (by norm_num) (by norm_num)
  obtain ⟨j81,hj81⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j52 j80=z := ⟨_,rfl⟩
  have j81_value : Bounds (1/128 : ℝ) j81.value (1/128 : ℝ) := by
    simpa only [← hj81,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h261
  have j81_tangent : Bounds (1/128 : ℝ) j81.tangent (1/128 : ℝ) := by
    simpa only [← hj81,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h264
  let v265 : ℝ := j79.value+j81.value
  have h265 : Bounds (-127/256 : ℝ) v265 (-127/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j79_value j81_value) (by norm_num) (by norm_num)
  let v266 : ℝ := j79.tangent+j81.tangent
  have h266 : Bounds (1/256 : ℝ) v266 (1/256 : ℝ) := by
    exact enlarge (IntervalBounds.add j79_tangent j81_tangent) (by norm_num) (by norm_num)
  obtain ⟨j82,hj82⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j79 j81=z := ⟨_,rfl⟩
  have j82_value : Bounds (-127/256 : ℝ) j82.value (-127/256 : ℝ) := by
    simpa only [← hj82,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h265
  have j82_tangent : Bounds (1/256 : ℝ) j82.tangent (1/256 : ℝ) := by
    simpa only [← hj82,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h266
  let v267 : ℝ := j78.value*j82.value
  have h267 : Bounds (127/1024 : ℝ) v267 (127/1024 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j78_value j82_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v268 : ℝ := j78.tangent*j82.value
  have h268 : Bounds (0 : ℝ) v268 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j78_tangent j82_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v269 : ℝ := j78.value*j82.tangent
  have h269 : Bounds (-1/1024 : ℝ) v269 (-1/1024 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j78_value j82_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v270 : ℝ := v268+v269
  have h270 : Bounds (-1/1024 : ℝ) v270 (-1/1024 : ℝ) := by
    exact enlarge (IntervalBounds.add h268 h269) (by norm_num) (by norm_num)
  obtain ⟨j83,hj83⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j78 j82=z := ⟨_,rfl⟩
  have j83_value : Bounds (127/1024 : ℝ) j83.value (127/1024 : ℝ) := by
    simpa only [← hj83,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h267
  have j83_tangent : Bounds (-1/1024 : ℝ) j83.tangent (-1/1024 : ℝ) := by
    simpa only [← hj83,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h270
  let v271 : ℝ := j77.value*j83.value
  have h271 : Bounds (8176129946711/50000000000000 : ℝ) v271 (16352259893423/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v272 : ℝ := j77.tangent*j83.value
  have h272 : Bounds (0 : ℝ) v272 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v273 : ℝ := j77.value*j83.tangent
  have h273 : Bounds (-128757951917/100000000000000 : ℝ) v273 (-32189487979/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j77_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v274 : ℝ := v272+v273
  have h274 : Bounds (-128757951917/100000000000000 : ℝ) v274 (-32189487979/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h272 h273) (by norm_num) (by norm_num)
  obtain ⟨j84,hj84⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j83=z := ⟨_,rfl⟩
  have j84_value : Bounds (8176129946711/50000000000000 : ℝ) j84.value (16352259893423/100000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h271
  have j84_tangent : Bounds (-128757951917/100000000000000 : ℝ) j84.tangent (-32189487979/25000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h274
  let v275 : ℝ := -(-1/8 : ℝ)
  have h275 : Bounds (1/8 : ℝ) v275 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (-1/8 : ℝ))) (by norm_num) (by norm_num)
  let v276 : ℝ := d+v275
  have h276 : Bounds (-3600928478703/4000000000000 : ℝ) v276 (-45011605983787/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hd h275) (by norm_num) (by norm_num)
  obtain ⟨j85,hj85⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (d+(-(-1/8 : ℝ)))=z := ⟨_,rfl⟩
  have j85_value : Bounds (-3600928478703/4000000000000 : ℝ) j85.value (-45011605983787/50000000000000 : ℝ) := by
    simpa only [← hj85,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h276
  have j85_tangent : Bounds (0 : ℝ) j85.tangent (0 : ℝ) := by
    simpa only [← hj85,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v277 : ℝ := j70.value*j4.value
  have h277 : Bounds (1/16 : ℝ) v277 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j70_value j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v278 : ℝ := j70.tangent*j4.value
  have h278 : Bounds (1/16 : ℝ) v278 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j70_tangent j4_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v279 : ℝ := j70.value*j4.tangent
  have h279 : Bounds (0 : ℝ) v279 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j70_value j4_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v280 : ℝ := v278+v279
  have h280 : Bounds (1/16 : ℝ) v280 (1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add h278 h279) (by norm_num) (by norm_num)
  obtain ⟨j86,hj86⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j70 j4=z := ⟨_,rfl⟩
  have j86_value : Bounds (1/16 : ℝ) j86.value (1/16 : ℝ) := by
    simpa only [← hj86,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h277
  have j86_tangent : Bounds (1/16 : ℝ) j86.tangent (1/16 : ℝ) := by
    simpa only [← hj86,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h280
  let v281 : ℝ := j76.value*j80.value
  have h281 : Bounds (-1/8 : ℝ) v281 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j76_value j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v282 : ℝ := j76.tangent*j80.value
  have h282 : Bounds (-1/8 : ℝ) v282 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j76_tangent j80_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v283 : ℝ := j76.value*j80.tangent
  have h283 : Bounds (0 : ℝ) v283 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j76_value j80_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v284 : ℝ := v282+v283
  have h284 : Bounds (-1/8 : ℝ) v284 (-1/8 : ℝ) := by
    exact enlarge (IntervalBounds.add h282 h283) (by norm_num) (by norm_num)
  obtain ⟨j87,hj87⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j76 j80=z := ⟨_,rfl⟩
  have j87_value : Bounds (-1/8 : ℝ) j87.value (-1/8 : ℝ) := by
    simpa only [← hj87,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h281
  have j87_tangent : Bounds (-1/8 : ℝ) j87.tangent (-1/8 : ℝ) := by
    simpa only [← hj87,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h284
  let v285 : ℝ := j86.value+j87.value
  have h285 : Bounds (-1/16 : ℝ) v285 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j86_value j87_value) (by norm_num) (by norm_num)
  let v286 : ℝ := j86.tangent+j87.tangent
  have h286 : Bounds (-1/16 : ℝ) v286 (-1/16 : ℝ) := by
    exact enlarge (IntervalBounds.add j86_tangent j87_tangent) (by norm_num) (by norm_num)
  obtain ⟨j88,hj88⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j86 j87=z := ⟨_,rfl⟩
  have j88_value : Bounds (-1/16 : ℝ) j88.value (-1/16 : ℝ) := by
    simpa only [← hj88,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h285
  have j88_tangent : Bounds (-1/16 : ℝ) j88.tangent (-1/16 : ℝ) := by
    simpa only [← hj88,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h286
  let v287 : ℝ := j78.value*j88.value
  have h287 : Bounds (1/64 : ℝ) v287 (1/64 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j78_value j88_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v288 : ℝ := j78.tangent*j88.value
  have h288 : Bounds (0 : ℝ) v288 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j78_tangent j88_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v289 : ℝ := j78.value*j88.tangent
  have h289 : Bounds (1/64 : ℝ) v289 (1/64 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j78_value j88_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v290 : ℝ := v288+v289
  have h290 : Bounds (1/64 : ℝ) v290 (1/64 : ℝ) := by
    exact enlarge (IntervalBounds.add h288 h289) (by norm_num) (by norm_num)
  obtain ⟨j89,hj89⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j78 j88=z := ⟨_,rfl⟩
  have j89_value : Bounds (1/64 : ℝ) j89.value (1/64 : ℝ) := by
    simpa only [← hj89,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h287
  have j89_tangent : Bounds (1/64 : ℝ) j89.tangent (1/64 : ℝ) := by
    simpa only [← hj89,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h290
  let v291 : ℝ := j85.value*j89.value
  have h291 : Bounds (-703306343497/50000000000000 : ℝ) v291 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v292 : ℝ := j85.tangent*j89.value
  have h292 : Bounds (0 : ℝ) v292 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v293 : ℝ := j85.value*j89.tangent
  have h293 : Bounds (-703306343497/50000000000000 : ℝ) v293 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v294 : ℝ := v292+v293
  have h294 : Bounds (-703306343497/50000000000000 : ℝ) v294 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h292 h293) (by norm_num) (by norm_num)
  obtain ⟨j90,hj90⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j89=z := ⟨_,rfl⟩
  have j90_value : Bounds (-703306343497/50000000000000 : ℝ) j90.value (-1406612686993/100000000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h291
  have j90_tangent : Bounds (-703306343497/50000000000000 : ℝ) j90.tangent (-1406612686993/100000000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h294
  let v295 : ℝ := j84.value+j90.value
  have h295 : Bounds (3736411801607/25000000000000 : ℝ) v295 (1494564720643/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_value j90_value) (by norm_num) (by norm_num)
  let v296 : ℝ := j84.tangent+j90.tangent
  have h296 : Bounds (-1535370638911/100000000000000 : ℝ) v296 (-1535370638909/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_tangent j90_tangent) (by norm_num) (by norm_num)
  obtain ⟨j91,hj91⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j84 j90=z := ⟨_,rfl⟩
  have j91_value : Bounds (3736411801607/25000000000000 : ℝ) j91.value (1494564720643/10000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h295
  have j91_tangent : Bounds (-1535370638911/100000000000000 : ℝ) j91.tangent (-1535370638909/100000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h296
  let v297 : ℝ := j91.value⁻¹
  have h297 : Bounds (669091131476577/100000000000000 : ℝ) v297 (167272782869167/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j91_value (by norm_num)) (by norm_num) (by norm_num)
  let v298 : ℝ := -j91.tangent
  have h298 : Bounds (1535370638909/100000000000000 : ℝ) v298 (1535370638911/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j91_tangent) (by norm_num) (by norm_num)
  let v299 : ℝ := j91.value*j91.value
  have h299 : Bounds (223372370419/10000000000000 : ℝ) v299 (2233723704191/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j91_value j91_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v300 : ℝ := v299⁻¹
  have h300 : Bounds (1119207355551361/25000000000000 : ℝ) v300 (4476829422207449/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h299 (by norm_num)) (by norm_num) (by norm_num)
  let v301 : ℝ := v298*v300
  have h301 : Bounds (68735924502581/100000000000000 : ℝ) v301 (68735924502703/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn h298 h300 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j92,hj92⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j91=z := ⟨_,rfl⟩
  have j92_value : Bounds (669091131476577/100000000000000 : ℝ) j92.value (167272782869167/25000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h297
  have j92_tangent : Bounds (68735924502581/100000000000000 : ℝ) j92.tangent (68735924502703/100000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h301
  let v302 : ℝ := j83.value*j77.value
  have h302 : Bounds (8176129946711/50000000000000 : ℝ) v302 (16352259893423/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v303 : ℝ := j83.tangent*j77.value
  have h303 : Bounds (-128757951917/100000000000000 : ℝ) v303 (-32189487979/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j83_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v304 : ℝ := j83.value*j77.tangent
  have h304 : Bounds (0 : ℝ) v304 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v305 : ℝ := v303+v304
  have h305 : Bounds (-128757951917/100000000000000 : ℝ) v305 (-32189487979/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h303 h304) (by norm_num) (by norm_num)
  obtain ⟨j93,hj93⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j77=z := ⟨_,rfl⟩
  have j93_value : Bounds (8176129946711/50000000000000 : ℝ) j93.value (16352259893423/100000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h302
  have j93_tangent : Bounds (-128757951917/100000000000000 : ℝ) j93.tangent (-32189487979/25000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h305
  let v306 : ℝ := j92.value*j93.value
  have h306 : Bounds (109411520742887/100000000000000 : ℝ) v306 (10941152074291/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v307 : ℝ := j92.tangent*j93.value
  have h307 : Bounds (1404984626851/12500000000000 : ℝ) v307 (1123987701483/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v308 : ℝ := j92.value*j93.tangent
  have h308 : Bounds (-215377009337/25000000000000 : ℝ) v308 (-43075401867/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j93_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v309 : ℝ := v307+v308
  have h309 : Bounds (518918448873/5000000000000 : ℝ) v309 (1037836897749/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h307 h308) (by norm_num) (by norm_num)
  obtain ⟨j94,hj94⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j93=z := ⟨_,rfl⟩
  have j94_value : Bounds (109411520742887/100000000000000 : ℝ) j94.value (10941152074291/10000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h306
  have j94_tangent : Bounds (518918448873/5000000000000 : ℝ) j94.tangent (1037836897749/10000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h309
  let v310 : ℝ := -j94.value
  have h310 : Bounds (-10941152074291/10000000000000 : ℝ) v310 (-109411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_value) (by norm_num) (by norm_num)
  let v311 : ℝ := j0.value+v310
  have h311 : Bounds (-941152074291/10000000000000 : ℝ) v311 (-9411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h310) (by norm_num) (by norm_num)
  let v312 : ℝ := -j94.tangent
  have h312 : Bounds (-1037836897749/10000000000000 : ℝ) v312 (-518918448873/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_tangent) (by norm_num) (by norm_num)
  let v313 : ℝ := j0.tangent+v312
  have h313 : Bounds (-1037836897749/10000000000000 : ℝ) v313 (-518918448873/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h312) (by norm_num) (by norm_num)
  obtain ⟨j95,hj95⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j94=z := ⟨_,rfl⟩
  have j95_value : Bounds (-941152074291/10000000000000 : ℝ) j95.value (-9411520742887/100000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h311
  have j95_tangent : Bounds (-1037836897749/10000000000000 : ℝ) j95.tangent (-518918448873/5000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h313
  let v314 : ℝ := j95.value*j41.value
  have h314 : Bounds (-4742524124357/100000000000000 : ℝ) v314 (-948504824869/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v315 : ℝ := j95.tangent*j41.value
  have h315 : Bounds (-1307431248141/25000000000000 : ℝ) v315 (-1307431248137/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v316 : ℝ := j95.value*j41.tangent
  have h316 : Bounds (-18381876451/50000000000000 : ℝ) v316 (-36763752901/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v317 : ℝ := v315+v316
  have h317 : Bounds (-2633244372733/50000000000000 : ℝ) v317 (-5266488745449/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h315 h316) (by norm_num) (by norm_num)
  obtain ⟨j96,hj96⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j41=z := ⟨_,rfl⟩
  have j96_value : Bounds (-4742524124357/100000000000000 : ℝ) j96.value (-948504824869/20000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h314
  have j96_tangent : Bounds (-2633244372733/50000000000000 : ℝ) j96.tangent (-5266488745449/100000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h317
  let v318 : ℝ := j83.value*j85.value
  have h318 : Bounds (-1116498820301/10000000000000 : ℝ) v318 (-11164988203009/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j83_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v319 : ℝ := j83.tangent*j85.value
  have h319 : Bounds (87913292937/100000000000000 : ℝ) v319 (43956646469/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j83_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v320 : ℝ := j83.value*j85.tangent
  have h320 : Bounds (0 : ℝ) v320 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v321 : ℝ := v319+v320
  have h321 : Bounds (87913292937/100000000000000 : ℝ) v321 (43956646469/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h319 h320) (by norm_num) (by norm_num)
  obtain ⟨j97,hj97⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j85=z := ⟨_,rfl⟩
  have j97_value : Bounds (-1116498820301/10000000000000 : ℝ) j97.value (-11164988203009/100000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h318
  have j97_tangent : Bounds (87913292937/100000000000000 : ℝ) j97.tangent (43956646469/50000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h321
  let v322 : ℝ := j92.value*j97.value
  have h322 : Bounds (-74703945896757/100000000000000 : ℝ) v322 (-74703945896739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v323 : ℝ := j92.tangent*j97.value
  have h323 : Bounds (-7674357861957/100000000000000 : ℝ) v323 (-3837178930971/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v324 : ℝ := j92.value*j97.tangent
  have h324 : Bounds (58822004643/10000000000000 : ℝ) v324 (294110023219/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j97_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v325 : ℝ := v323+v324
  have h325 : Bounds (-7086137815527/100000000000000 : ℝ) v325 (-442883613469/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h323 h324) (by norm_num) (by norm_num)
  obtain ⟨j98,hj98⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j97=z := ⟨_,rfl⟩
  have j98_value : Bounds (-74703945896757/100000000000000 : ℝ) j98.value (-74703945896739/100000000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h322
  have j98_tangent : Bounds (-7086137815527/100000000000000 : ℝ) j98.tangent (-442883613469/6250000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h325
  let v326 : ℝ := -j98.value
  have h326 : Bounds (74703945896739/100000000000000 : ℝ) v326 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_value) (by norm_num) (by norm_num)
  let v327 : ℝ := j6.value+v326
  have h327 : Bounds (74703945896739/100000000000000 : ℝ) v327 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h326) (by norm_num) (by norm_num)
  let v328 : ℝ := -j98.tangent
  have h328 : Bounds (442883613469/6250000000000 : ℝ) v328 (7086137815527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_tangent) (by norm_num) (by norm_num)
  let v329 : ℝ := j6.tangent+v328
  have h329 : Bounds (442883613469/6250000000000 : ℝ) v329 (7086137815527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h328) (by norm_num) (by norm_num)
  obtain ⟨j99,hj99⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j98=z := ⟨_,rfl⟩
  have j99_value : Bounds (74703945896739/100000000000000 : ℝ) j99.value (74703945896757/100000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h327
  have j99_tangent : Bounds (442883613469/6250000000000 : ℝ) j99.tangent (7086137815527/100000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h329
  let v330 : ℝ := j99.value*j70.value
  have h330 : Bounds (-1167249154637/25000000000000 : ℝ) v330 (-2334498309273/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v331 : ℝ := j99.tangent*j70.value
  have h331 : Bounds (-442883613471/100000000000000 : ℝ) v331 (-442883613469/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v332 : ℝ := j99.value*j70.tangent
  have h332 : Bounds (-1167249154637/25000000000000 : ℝ) v332 (-2334498309273/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v333 : ℝ := v331+v332
  have h333 : Bounds (-5111880232019/100000000000000 : ℝ) v333 (-1022376046403/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h331 h332) (by norm_num) (by norm_num)
  obtain ⟨j100,hj100⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j70=z := ⟨_,rfl⟩
  have j100_value : Bounds (-1167249154637/25000000000000 : ℝ) j100.value (-2334498309273/50000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h330
  have j100_tangent : Bounds (-5111880232019/100000000000000 : ℝ) j100.tangent (-1022376046403/20000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h333
  let v334 : ℝ := j96.value+j100.value
  have h334 : Bounds (-1882304148581/20000000000000 : ℝ) v334 (-9411520742891/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_value j100_value) (by norm_num) (by norm_num)
  let v335 : ℝ := j96.tangent+j100.tangent
  have h335 : Bounds (-2075673795497/20000000000000 : ℝ) v335 (-1297296122183/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_tangent j100_tangent) (by norm_num) (by norm_num)
  obtain ⟨j101,hj101⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j96 j100=z := ⟨_,rfl⟩
  have j101_value : Bounds (-1882304148581/20000000000000 : ℝ) j101.value (-9411520742891/100000000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h334
  have j101_tangent : Bounds (-2075673795497/20000000000000 : ℝ) j101.tangent (-1297296122183/12500000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h335
  let v336 : ℝ := j92.value*j84.value
  have h336 : Bounds (109411520742887/100000000000000 : ℝ) v336 (10941152074291/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v337 : ℝ := j92.tangent*j84.value
  have h337 : Bounds (1404984626851/12500000000000 : ℝ) v337 (1123987701483/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v338 : ℝ := j92.value*j84.tangent
  have h338 : Bounds (-215377009337/25000000000000 : ℝ) v338 (-43075401867/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j84_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v339 : ℝ := v337+v338
  have h339 : Bounds (518918448873/5000000000000 : ℝ) v339 (1037836897749/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h337 h338) (by norm_num) (by norm_num)
  obtain ⟨j102,hj102⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j84=z := ⟨_,rfl⟩
  have j102_value : Bounds (109411520742887/100000000000000 : ℝ) j102.value (10941152074291/10000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h336
  have j102_tangent : Bounds (518918448873/5000000000000 : ℝ) j102.tangent (1037836897749/10000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h339
  let v340 : ℝ := -j102.value
  have h340 : Bounds (-10941152074291/10000000000000 : ℝ) v340 (-109411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_value) (by norm_num) (by norm_num)
  let v341 : ℝ := j0.value+v340
  have h341 : Bounds (-941152074291/10000000000000 : ℝ) v341 (-9411520742887/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h340) (by norm_num) (by norm_num)
  let v342 : ℝ := -j102.tangent
  have h342 : Bounds (-1037836897749/10000000000000 : ℝ) v342 (-518918448873/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_tangent) (by norm_num) (by norm_num)
  let v343 : ℝ := j0.tangent+v342
  have h343 : Bounds (-1037836897749/10000000000000 : ℝ) v343 (-518918448873/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h342) (by norm_num) (by norm_num)
  obtain ⟨j103,hj103⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j102=z := ⟨_,rfl⟩
  have j103_value : Bounds (-941152074291/10000000000000 : ℝ) j103.value (-9411520742887/100000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h341
  have j103_tangent : Bounds (-1037836897749/10000000000000 : ℝ) j103.tangent (-518918448873/5000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h343
  let v344 : ℝ := j101.value*j103.value
  have h344 : Bounds (442883613469/50000000000000 : ℝ) v344 (442883613471/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v345 : ℝ := j101.tangent*j103.value
  have h345 : Bounds (976762349087/100000000000000 : ℝ) v345 (244190587273/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v346 : ℝ := j101.value*j103.tangent
  have h346 : Bounds (976762349087/100000000000000 : ℝ) v346 (244190587273/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v347 : ℝ := v345+v346
  have h347 : Bounds (976762349087/50000000000000 : ℝ) v347 (244190587273/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h345 h346) (by norm_num) (by norm_num)
  obtain ⟨j104,hj104⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j103=z := ⟨_,rfl⟩
  have j104_value : Bounds (442883613469/50000000000000 : ℝ) j104.value (442883613471/50000000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h344
  have j104_tangent : Bounds (976762349087/50000000000000 : ℝ) j104.tangent (244190587273/12500000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h347
  let v348 : ℝ := j95.value*j52.value
  have h348 : Bounds (58822004643/10000000000000 : ℝ) v348 (18381876451/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v349 : ℝ := j95.tangent*j52.value
  have h349 : Bounds (648648061091/100000000000000 : ℝ) v349 (324324030547/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v350 : ℝ := j95.value*j52.tangent
  have h350 : Bounds (58822004643/10000000000000 : ℝ) v350 (18381876451/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v351 : ℝ := v349+v350
  have h351 : Bounds (1236868107521/100000000000000 : ℝ) v351 (618434053763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h349 h350) (by norm_num) (by norm_num)
  obtain ⟨j105,hj105⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j52=z := ⟨_,rfl⟩
  have j105_value : Bounds (58822004643/10000000000000 : ℝ) j105.value (18381876451/3125000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h348
  have j105_tangent : Bounds (1236868107521/100000000000000 : ℝ) j105.tangent (618434053763/50000000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h351
  let v352 : ℝ := j99.value*j76.value
  have h352 : Bounds (74703945896739/100000000000000 : ℝ) v352 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v353 : ℝ := j99.tangent*j76.value
  have h353 : Bounds (442883613469/6250000000000 : ℝ) v353 (7086137815527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v354 : ℝ := j99.value*j76.tangent
  have h354 : Bounds (74703945896739/100000000000000 : ℝ) v354 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v355 : ℝ := v353+v354
  have h355 : Bounds (81790083712243/100000000000000 : ℝ) v355 (20447520928071/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h353 h354) (by norm_num) (by norm_num)
  obtain ⟨j106,hj106⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j76=z := ⟨_,rfl⟩
  have j106_value : Bounds (74703945896739/100000000000000 : ℝ) j106.value (74703945896757/100000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h352
  have j106_tangent : Bounds (81790083712243/100000000000000 : ℝ) j106.tangent (20447520928071/25000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h355
  let v356 : ℝ := j105.value+j106.value
  have h356 : Bounds (75292165943169/100000000000000 : ℝ) v356 (75292165943189/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_value j106_value) (by norm_num) (by norm_num)
  let v357 : ℝ := j105.tangent+j106.tangent
  have h357 : Bounds (20756737954941/25000000000000 : ℝ) v357 (8302695181981/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_tangent j106_tangent) (by norm_num) (by norm_num)
  obtain ⟨j107,hj107⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j105 j106=z := ⟨_,rfl⟩
  have j107_value : Bounds (75292165943169/100000000000000 : ℝ) j107.value (75292165943189/100000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h356
  have j107_tangent : Bounds (20756737954941/25000000000000 : ℝ) j107.tangent (8302695181981/10000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h357
  let v358 : ℝ := j85.value*j83.value
  have h358 : Bounds (-1116498820301/10000000000000 : ℝ) v358 (-11164988203009/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v359 : ℝ := j85.tangent*j83.value
  have h359 : Bounds (0 : ℝ) v359 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v360 : ℝ := j85.value*j83.tangent
  have h360 : Bounds (87913292937/100000000000000 : ℝ) v360 (43956646469/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j85_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v361 : ℝ := v359+v360
  have h361 : Bounds (87913292937/100000000000000 : ℝ) v361 (43956646469/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h359 h360) (by norm_num) (by norm_num)
  obtain ⟨j108,hj108⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j83=z := ⟨_,rfl⟩
  have j108_value : Bounds (-1116498820301/10000000000000 : ℝ) j108.value (-11164988203009/100000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h358
  have j108_tangent : Bounds (87913292937/100000000000000 : ℝ) j108.tangent (43956646469/50000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h361
  let v362 : ℝ := j92.value*j108.value
  have h362 : Bounds (-74703945896757/100000000000000 : ℝ) v362 (-74703945896739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v363 : ℝ := j92.tangent*j108.value
  have h363 : Bounds (-7674357861957/100000000000000 : ℝ) v363 (-3837178930971/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v364 : ℝ := j92.value*j108.tangent
  have h364 : Bounds (58822004643/10000000000000 : ℝ) v364 (294110023219/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j108_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v365 : ℝ := v363+v364
  have h365 : Bounds (-7086137815527/100000000000000 : ℝ) v365 (-442883613469/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h363 h364) (by norm_num) (by norm_num)
  obtain ⟨j109,hj109⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j108=z := ⟨_,rfl⟩
  have j109_value : Bounds (-74703945896757/100000000000000 : ℝ) j109.value (-74703945896739/100000000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h362
  have j109_tangent : Bounds (-7086137815527/100000000000000 : ℝ) j109.tangent (-442883613469/6250000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h365
  let v366 : ℝ := -j109.value
  have h366 : Bounds (74703945896739/100000000000000 : ℝ) v366 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_value) (by norm_num) (by norm_num)
  let v367 : ℝ := j6.value+v366
  have h367 : Bounds (74703945896739/100000000000000 : ℝ) v367 (74703945896757/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h366) (by norm_num) (by norm_num)
  let v368 : ℝ := -j109.tangent
  have h368 : Bounds (442883613469/6250000000000 : ℝ) v368 (7086137815527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_tangent) (by norm_num) (by norm_num)
  let v369 : ℝ := j6.tangent+v368
  have h369 : Bounds (442883613469/6250000000000 : ℝ) v369 (7086137815527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h368) (by norm_num) (by norm_num)
  obtain ⟨j110,hj110⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j109=z := ⟨_,rfl⟩
  have j110_value : Bounds (74703945896739/100000000000000 : ℝ) j110.value (74703945896757/100000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h367
  have j110_tangent : Bounds (442883613469/6250000000000 : ℝ) j110.tangent (7086137815527/100000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h369
  let v370 : ℝ := j107.value*j110.value
  have h370 : Bounds (56246218910667/100000000000000 : ℝ) v370 (56246218910697/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v371 : ℝ := j107.tangent*j110.value
  have h371 : Bounds (15506102291787/25000000000000 : ℝ) v371 (31012204583599/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v372 : ℝ := j107.value*j110.tangent
  have h372 : Bounds (533530664301/10000000000000 : ℝ) v372 (533530664303/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v373 : ℝ := v371+v372
  have h373 : Bounds (33679857905079/50000000000000 : ℝ) v373 (16839928952557/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h371 h372) (by norm_num) (by norm_num)
  obtain ⟨j111,hj111⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j110=z := ⟨_,rfl⟩
  have j111_value : Bounds (56246218910667/100000000000000 : ℝ) j111.value (56246218910697/100000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h370
  have j111_tangent : Bounds (33679857905079/50000000000000 : ℝ) j111.tangent (16839928952557/25000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h373
  let v374 : ℝ := j104.value+j111.value
  have h374 : Bounds (11426397227521/20000000000000 : ℝ) v374 (57131986137639/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_value j111_value) (by norm_num) (by norm_num)
  let v375 : ℝ := j104.tangent+j111.tangent
  have h375 : Bounds (17328310127083/25000000000000 : ℝ) v375 (17328310127103/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_tangent j111_tangent) (by norm_num) (by norm_num)
  obtain ⟨j112,hj112⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j104 j111=z := ⟨_,rfl⟩
  have j112_value : Bounds (11426397227521/20000000000000 : ℝ) j112.value (57131986137639/100000000000000 : ℝ) := by
    simpa only [← hj112,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h374
  have j112_tangent : Bounds (17328310127083/25000000000000 : ℝ) j112.tangent (17328310127103/25000000000000 : ℝ) := by
    simpa only [← hj112,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h375
  let v376 : ℝ := j83.value*j83.value
  have h376 : Bounds (16129/1048576 : ℝ) v376 (16129/1048576 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v377 : ℝ := j83.tangent*j83.value
  have h377 : Bounds (-127/1048576 : ℝ) v377 (-127/1048576 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j83_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v378 : ℝ := j83.value*j83.tangent
  have h378 : Bounds (-127/1048576 : ℝ) v378 (-127/1048576 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j83_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v379 : ℝ := v377+v378
  have h379 : Bounds (-127/524288 : ℝ) v379 (-127/524288 : ℝ) := by
    exact enlarge (IntervalBounds.add h377 h378) (by norm_num) (by norm_num)
  obtain ⟨j113,hj113⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j83=z := ⟨_,rfl⟩
  have j113_value : Bounds (16129/1048576 : ℝ) j113.value (16129/1048576 : ℝ) := by
    simpa only [← hj113,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h376
  have j113_tangent : Bounds (-127/524288 : ℝ) j113.tangent (-127/524288 : ℝ) := by
    simpa only [← hj113,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h379
  let v380 : ℝ := j92.value*j113.value
  have h380 : Bounds (643239668583/6250000000000 : ℝ) v380 (1029183469733/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v381 : ℝ := j92.tangent*j113.value
  have h381 : Bounds (105728314047/10000000000000 : ℝ) v381 (1057283140473/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v382 : ℝ := j92.value*j113.tangent
  have h382 : Bounds (-81038068483/50000000000000 : ℝ) v382 (-32415227393/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j113_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v383 : ℝ := v381+v382
  have h383 : Bounds (55950437719/6250000000000 : ℝ) v383 (223801750877/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h381 h382) (by norm_num) (by norm_num)
  obtain ⟨j114,hj114⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j113=z := ⟨_,rfl⟩
  have j114_value : Bounds (643239668583/6250000000000 : ℝ) j114.value (1029183469733/10000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h380
  have j114_tangent : Bounds (55950437719/6250000000000 : ℝ) j114.tangent (223801750877/25000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h383
  let v384 : ℝ := j112.value+j114.value
  have h384 : Bounds (67423820834933/100000000000000 : ℝ) v384 (67423820834969/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_value j114_value) (by norm_num) (by norm_num)
  let v385 : ℝ := j112.tangent+j114.tangent
  have h385 : Bounds (17552111877959/25000000000000 : ℝ) v385 (877605593899/1250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_tangent j114_tangent) (by norm_num) (by norm_num)
  obtain ⟨j115,hj115⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j112 j114=z := ⟨_,rfl⟩
  have j115_value : Bounds (67423820834933/100000000000000 : ℝ) j115.value (67423820834969/100000000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h384
  have j115_tangent : Bounds (17552111877959/25000000000000 : ℝ) j115.tangent (877605593899/1250000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h385
  let v386 : ℝ := j77.value*j89.value
  have h386 : Bounds (2060127230667/100000000000000 : ℝ) v386 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v387 : ℝ := j77.tangent*j89.value
  have h387 : Bounds (0 : ℝ) v387 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v388 : ℝ := j77.value*j89.tangent
  have h388 : Bounds (2060127230667/100000000000000 : ℝ) v388 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v389 : ℝ := v387+v388
  have h389 : Bounds (2060127230667/100000000000000 : ℝ) v389 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h387 h388) (by norm_num) (by norm_num)
  obtain ⟨j116,hj116⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j89=z := ⟨_,rfl⟩
  have j116_value : Bounds (2060127230667/100000000000000 : ℝ) j116.value (515031807667/25000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h386
  have j116_tangent : Bounds (2060127230667/100000000000000 : ℝ) j116.tangent (515031807667/25000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h389
  let v390 : ℝ := j92.value*j116.value
  have h390 : Bounds (6892064298763/50000000000000 : ℝ) v390 (430754018673/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v391 : ℝ := j92.tangent*j116.value
  have h391 : Bounds (177005937241/12500000000000 : ℝ) v391 (354011874483/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v392 : ℝ := j92.value*j116.tangent
  have h392 : Bounds (6892064298763/50000000000000 : ℝ) v392 (430754018673/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v393 : ℝ := v391+v392
  have h393 : Bounds (7600088047727/50000000000000 : ℝ) v393 (3800044023867/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h391 h392) (by norm_num) (by norm_num)
  obtain ⟨j117,hj117⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j116=z := ⟨_,rfl⟩
  have j117_value : Bounds (6892064298763/50000000000000 : ℝ) j117.value (430754018673/3125000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h390
  have j117_tangent : Bounds (7600088047727/50000000000000 : ℝ) j117.tangent (3800044023867/25000000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h393
  let v394 : ℝ := -j117.value
  have h394 : Bounds (-430754018673/3125000000000 : ℝ) v394 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_value) (by norm_num) (by norm_num)
  let v395 : ℝ := j6.value+v394
  have h395 : Bounds (-430754018673/3125000000000 : ℝ) v395 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h394) (by norm_num) (by norm_num)
  let v396 : ℝ := -j117.tangent
  have h396 : Bounds (-3800044023867/25000000000000 : ℝ) v396 (-7600088047727/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_tangent) (by norm_num) (by norm_num)
  let v397 : ℝ := j6.tangent+v396
  have h397 : Bounds (-3800044023867/25000000000000 : ℝ) v397 (-7600088047727/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h396) (by norm_num) (by norm_num)
  obtain ⟨j118,hj118⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j117=z := ⟨_,rfl⟩
  have j118_value : Bounds (-430754018673/3125000000000 : ℝ) j118.value (-6892064298763/50000000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h395
  have j118_tangent : Bounds (-3800044023867/25000000000000 : ℝ) j118.tangent (-7600088047727/50000000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h397
  let v398 : ℝ := j101.value*j118.value
  have h398 : Bounds (648648061091/50000000000000 : ℝ) v398 (648648061093/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v399 : ℝ := j101.tangent*j118.value
  have h399 : Bounds (1430567726179/100000000000000 : ℝ) v399 (178820965773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v400 : ℝ := j101.value*j118.tangent
  have h400 : Bounds (1430567726179/100000000000000 : ℝ) v400 (178820965773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v401 : ℝ := v399+v400
  have h401 : Bounds (1430567726179/50000000000000 : ℝ) v401 (178820965773/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h399 h400) (by norm_num) (by norm_num)
  obtain ⟨j119,hj119⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j118=z := ⟨_,rfl⟩
  have j119_value : Bounds (648648061091/50000000000000 : ℝ) j119.value (648648061093/50000000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h398
  have j119_tangent : Bounds (1430567726179/50000000000000 : ℝ) j119.tangent (178820965773/6250000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h401
  let v402 : ℝ := j92.value*j90.value
  have h402 : Bounds (-9411520742903/100000000000000 : ℝ) v402 (-4705760371447/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v403 : ℝ := j92.tangent*j90.value
  have h403 : Bounds (-483424117289/50000000000000 : ℝ) v403 (-38673929383/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v404 : ℝ := j92.value*j90.tangent
  have h404 : Bounds (-9411520742903/100000000000000 : ℝ) v404 (-4705760371447/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v405 : ℝ := v403+v404
  have h405 : Bounds (-10378368977481/100000000000000 : ℝ) v405 (-10378368977469/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h403 h404) (by norm_num) (by norm_num)
  obtain ⟨j120,hj120⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j90=z := ⟨_,rfl⟩
  have j120_value : Bounds (-9411520742903/100000000000000 : ℝ) j120.value (-4705760371447/50000000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h402
  have j120_tangent : Bounds (-10378368977481/100000000000000 : ℝ) j120.tangent (-10378368977469/100000000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h405
  let v406 : ℝ := -j120.value
  have h406 : Bounds (4705760371447/50000000000000 : ℝ) v406 (9411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_value) (by norm_num) (by norm_num)
  let v407 : ℝ := j0.value+v406
  have h407 : Bounds (54705760371447/50000000000000 : ℝ) v407 (109411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h406) (by norm_num) (by norm_num)
  let v408 : ℝ := -j120.tangent
  have h408 : Bounds (10378368977469/100000000000000 : ℝ) v408 (10378368977481/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_tangent) (by norm_num) (by norm_num)
  let v409 : ℝ := j0.tangent+v408
  have h409 : Bounds (10378368977469/100000000000000 : ℝ) v409 (10378368977481/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h408) (by norm_num) (by norm_num)
  obtain ⟨j121,hj121⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j120=z := ⟨_,rfl⟩
  have j121_value : Bounds (54705760371447/50000000000000 : ℝ) j121.value (109411520742903/100000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h407
  have j121_tangent : Bounds (10378368977469/100000000000000 : ℝ) j121.tangent (10378368977481/100000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h409
  let v410 : ℝ := j107.value*j121.value
  have h410 : Bounds (20594575939671/25000000000000 : ℝ) v410 (41189151879357/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v411 : ℝ := j107.tangent*j121.value
  have h411 : Bounds (90841050612473/100000000000000 : ℝ) v411 (22710262653133/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v412 : ℝ := j107.value*j121.tangent
  have h412 : Bounds (781409879271/10000000000000 : ℝ) v412 (3907049396361/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v413 : ℝ := v411+v412
  have h413 : Bounds (98655149405183/100000000000000 : ℝ) v413 (49327574702627/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h411 h412) (by norm_num) (by norm_num)
  obtain ⟨j122,hj122⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j121=z := ⟨_,rfl⟩
  have j122_value : Bounds (20594575939671/25000000000000 : ℝ) j122.value (41189151879357/50000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h410
  have j122_tangent : Bounds (98655149405183/100000000000000 : ℝ) j122.tangent (49327574702627/50000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h413
  let v414 : ℝ := j119.value+j122.value
  have h414 : Bounds (41837799940433/50000000000000 : ℝ) v414 (836755998809/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_value j122_value) (by norm_num) (by norm_num)
  let v415 : ℝ := j119.tangent+j122.tangent
  have h415 : Bounds (101516284857541/100000000000000 : ℝ) v415 (50758142428811/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_tangent j122_tangent) (by norm_num) (by norm_num)
  obtain ⟨j123,hj123⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j119 j122=z := ⟨_,rfl⟩
  have j123_value : Bounds (41837799940433/50000000000000 : ℝ) j123.value (836755998809/1000000000000 : ℝ) := by
    simpa only [← hj123,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h414
  have j123_tangent : Bounds (101516284857541/100000000000000 : ℝ) j123.tangent (50758142428811/50000000000000 : ℝ) := by
    simpa only [← hj123,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h415
  let v416 : ℝ := j83.value*j89.value
  have h416 : Bounds (127/65536 : ℝ) v416 (127/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v417 : ℝ := j83.tangent*j89.value
  have h417 : Bounds (-1/65536 : ℝ) v417 (-1/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j83_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v418 : ℝ := j83.value*j89.tangent
  have h418 : Bounds (127/65536 : ℝ) v418 (127/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v419 : ℝ := v417+v418
  have h419 : Bounds (63/32768 : ℝ) v419 (63/32768 : ℝ) := by
    exact enlarge (IntervalBounds.add h417 h418) (by norm_num) (by norm_num)
  obtain ⟨j124,hj124⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j89=z := ⟨_,rfl⟩
  have j124_value : Bounds (127/65536 : ℝ) j124.value (127/65536 : ℝ) := by
    simpa only [← hj124,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h416
  have j124_tangent : Bounds (63/32768 : ℝ) j124.tangent (63/32768 : ℝ) := by
    simpa only [← hj124,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h419
  let v420 : ℝ := j92.value*j124.value
  have h420 : Bounds (648304547863/50000000000000 : ℝ) v420 (1296609095727/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v421 : ℝ := j92.tangent*j124.value
  have h421 : Bounds (133201025571/100000000000000 : ℝ) v421 (33300256393/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v422 : ℝ := j92.value*j124.tangent
  have h422 : Bounds (1286399575287/100000000000000 : ℝ) v422 (160799946911/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v423 : ℝ := v421+v422
  have h423 : Bounds (709800300429/50000000000000 : ℝ) v423 (70980030043/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h421 h422) (by norm_num) (by norm_num)
  obtain ⟨j125,hj125⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j124=z := ⟨_,rfl⟩
  have j125_value : Bounds (648304547863/50000000000000 : ℝ) j125.value (1296609095727/100000000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h420
  have j125_tangent : Bounds (709800300429/50000000000000 : ℝ) j125.tangent (70980030043/5000000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h423
  let v424 : ℝ := j123.value+j125.value
  have h424 : Bounds (5310763061037/6250000000000 : ℝ) v424 (84972208976627/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_value j125_value) (by norm_num) (by norm_num)
  let v425 : ℝ := j123.tangent+j125.tangent
  have h425 : Bounds (102935885458399/100000000000000 : ℝ) v425 (51467942729241/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_tangent j125_tangent) (by norm_num) (by norm_num)
  obtain ⟨j126,hj126⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j123 j125=z := ⟨_,rfl⟩
  have j126_value : Bounds (5310763061037/6250000000000 : ℝ) j126.value (84972208976627/100000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h424
  have j126_tangent : Bounds (102935885458399/100000000000000 : ℝ) j126.tangent (51467942729241/50000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h425
  let v426 : ℝ := j89.value*j77.value
  have h426 : Bounds (2060127230667/100000000000000 : ℝ) v426 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v427 : ℝ := j89.tangent*j77.value
  have h427 : Bounds (2060127230667/100000000000000 : ℝ) v427 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v428 : ℝ := j89.value*j77.tangent
  have h428 : Bounds (0 : ℝ) v428 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v429 : ℝ := v427+v428
  have h429 : Bounds (2060127230667/100000000000000 : ℝ) v429 (515031807667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h427 h428) (by norm_num) (by norm_num)
  obtain ⟨j127,hj127⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j77=z := ⟨_,rfl⟩
  have j127_value : Bounds (2060127230667/100000000000000 : ℝ) j127.value (515031807667/25000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h426
  have j127_tangent : Bounds (2060127230667/100000000000000 : ℝ) j127.tangent (515031807667/25000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h429
  let v430 : ℝ := j92.value*j127.value
  have h430 : Bounds (6892064298763/50000000000000 : ℝ) v430 (430754018673/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v431 : ℝ := j92.tangent*j127.value
  have h431 : Bounds (177005937241/12500000000000 : ℝ) v431 (354011874483/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v432 : ℝ := j92.value*j127.tangent
  have h432 : Bounds (6892064298763/50000000000000 : ℝ) v432 (430754018673/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v433 : ℝ := v431+v432
  have h433 : Bounds (7600088047727/50000000000000 : ℝ) v433 (3800044023867/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h431 h432) (by norm_num) (by norm_num)
  obtain ⟨j128,hj128⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j127=z := ⟨_,rfl⟩
  have j128_value : Bounds (6892064298763/50000000000000 : ℝ) j128.value (430754018673/3125000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h430
  have j128_tangent : Bounds (7600088047727/50000000000000 : ℝ) j128.tangent (3800044023867/25000000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h433
  let v434 : ℝ := -j128.value
  have h434 : Bounds (-430754018673/3125000000000 : ℝ) v434 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_value) (by norm_num) (by norm_num)
  let v435 : ℝ := j6.value+v434
  have h435 : Bounds (-430754018673/3125000000000 : ℝ) v435 (-6892064298763/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h434) (by norm_num) (by norm_num)
  let v436 : ℝ := -j128.tangent
  have h436 : Bounds (-3800044023867/25000000000000 : ℝ) v436 (-7600088047727/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_tangent) (by norm_num) (by norm_num)
  let v437 : ℝ := j6.tangent+v436
  have h437 : Bounds (-3800044023867/25000000000000 : ℝ) v437 (-7600088047727/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h436) (by norm_num) (by norm_num)
  obtain ⟨j129,hj129⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j128=z := ⟨_,rfl⟩
  have j129_value : Bounds (-430754018673/3125000000000 : ℝ) j129.value (-6892064298763/50000000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h435
  have j129_tangent : Bounds (-3800044023867/25000000000000 : ℝ) j129.tangent (-7600088047727/50000000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h437
  let v438 : ℝ := j129.value*j41.value
  have h438 : Bounds (-6945908551103/100000000000000 : ℝ) v438 (-6945908551097/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v439 : ℝ := j129.tangent*j41.value
  have h439 : Bounds (-7659463735607/100000000000000 : ℝ) v439 (-7659463735599/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v440 : ℝ := j129.value*j41.tangent
  have h440 : Bounds (-10768850467/20000000000000 : ℝ) v440 (-26922126167/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v441 : ℝ := v439+v440
  have h441 : Bounds (-3856653993971/50000000000000 : ℝ) v441 (-7713307987933/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h439 h440) (by norm_num) (by norm_num)
  obtain ⟨j130,hj130⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j41=z := ⟨_,rfl⟩
  have j130_value : Bounds (-6945908551103/100000000000000 : ℝ) j130.value (-6945908551097/100000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h438
  have j130_tangent : Bounds (-3856653993971/50000000000000 : ℝ) j130.tangent (-7713307987933/100000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h441
  let v442 : ℝ := j89.value*j85.value
  have h442 : Bounds (-703306343497/50000000000000 : ℝ) v442 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v443 : ℝ := j89.tangent*j85.value
  have h443 : Bounds (-703306343497/50000000000000 : ℝ) v443 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v444 : ℝ := j89.value*j85.tangent
  have h444 : Bounds (0 : ℝ) v444 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v445 : ℝ := v443+v444
  have h445 : Bounds (-703306343497/50000000000000 : ℝ) v445 (-1406612686993/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h443 h444) (by norm_num) (by norm_num)
  obtain ⟨j131,hj131⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j85=z := ⟨_,rfl⟩
  have j131_value : Bounds (-703306343497/50000000000000 : ℝ) j131.value (-1406612686993/100000000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h442
  have j131_tangent : Bounds (-703306343497/50000000000000 : ℝ) j131.tangent (-1406612686993/100000000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h445
  let v446 : ℝ := j92.value*j131.value
  have h446 : Bounds (-9411520742903/100000000000000 : ℝ) v446 (-4705760371447/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v447 : ℝ := j92.tangent*j131.value
  have h447 : Bounds (-483424117289/50000000000000 : ℝ) v447 (-38673929383/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v448 : ℝ := j92.value*j131.tangent
  have h448 : Bounds (-9411520742903/100000000000000 : ℝ) v448 (-4705760371447/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v449 : ℝ := v447+v448
  have h449 : Bounds (-10378368977481/100000000000000 : ℝ) v449 (-10378368977469/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h447 h448) (by norm_num) (by norm_num)
  obtain ⟨j132,hj132⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j131=z := ⟨_,rfl⟩
  have j132_value : Bounds (-9411520742903/100000000000000 : ℝ) j132.value (-4705760371447/50000000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h446
  have j132_tangent : Bounds (-10378368977481/100000000000000 : ℝ) j132.tangent (-10378368977469/100000000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h449
  let v450 : ℝ := -j132.value
  have h450 : Bounds (4705760371447/50000000000000 : ℝ) v450 (9411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_value) (by norm_num) (by norm_num)
  let v451 : ℝ := j0.value+v450
  have h451 : Bounds (54705760371447/50000000000000 : ℝ) v451 (109411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h450) (by norm_num) (by norm_num)
  let v452 : ℝ := -j132.tangent
  have h452 : Bounds (10378368977469/100000000000000 : ℝ) v452 (10378368977481/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_tangent) (by norm_num) (by norm_num)
  let v453 : ℝ := j0.tangent+v452
  have h453 : Bounds (10378368977469/100000000000000 : ℝ) v453 (10378368977481/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h452) (by norm_num) (by norm_num)
  obtain ⟨j133,hj133⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j132=z := ⟨_,rfl⟩
  have j133_value : Bounds (54705760371447/50000000000000 : ℝ) j133.value (109411520742903/100000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h451
  have j133_tangent : Bounds (10378368977469/100000000000000 : ℝ) j133.tangent (10378368977481/100000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h453
  let v454 : ℝ := j133.value*j70.value
  have h454 : Bounds (-213694376451/3125000000000 : ℝ) v454 (-683822004643/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v455 : ℝ := j133.tangent*j70.value
  have h455 : Bounds (-648648061093/100000000000000 : ℝ) v455 (-648648061091/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v456 : ℝ := j133.value*j70.tangent
  have h456 : Bounds (-213694376451/3125000000000 : ℝ) v456 (-683822004643/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v457 : ℝ := v455+v456
  have h457 : Bounds (-299474724301/4000000000000 : ℝ) v457 (-7486868107521/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h455 h456) (by norm_num) (by norm_num)
  obtain ⟨j134,hj134⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j70=z := ⟨_,rfl⟩
  have j134_value : Bounds (-213694376451/3125000000000 : ℝ) j134.value (-683822004643/10000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h454
  have j134_tangent : Bounds (-299474724301/4000000000000 : ℝ) j134.tangent (-7486868107521/100000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h457
  let v458 : ℝ := j130.value+j134.value
  have h458 : Bounds (-2756825719507/20000000000000 : ℝ) v458 (-13784128597527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_value j134_value) (by norm_num) (by norm_num)
  let v459 : ℝ := j130.tangent+j134.tangent
  have h459 : Bounds (-15200176095467/100000000000000 : ℝ) v459 (-7600088047727/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_tangent j134_tangent) (by norm_num) (by norm_num)
  obtain ⟨j135,hj135⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j130 j134=z := ⟨_,rfl⟩
  have j135_value : Bounds (-2756825719507/20000000000000 : ℝ) j135.value (-13784128597527/100000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h458
  have j135_tangent : Bounds (-15200176095467/100000000000000 : ℝ) j135.tangent (-7600088047727/50000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h459
  let v460 : ℝ := j135.value*j103.value
  have h460 : Bounds (648648061091/50000000000000 : ℝ) v460 (1297296122187/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v461 : ℝ := j135.tangent*j103.value
  have h461 : Bounds (1430567726179/100000000000000 : ℝ) v461 (178820965773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v462 : ℝ := j135.value*j103.tangent
  have h462 : Bounds (715283863089/50000000000000 : ℝ) v462 (178820965773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v463 : ℝ := v461+v462
  have h463 : Bounds (2861135452357/100000000000000 : ℝ) v463 (178820965773/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h461 h462) (by norm_num) (by norm_num)
  obtain ⟨j136,hj136⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j103=z := ⟨_,rfl⟩
  have j136_value : Bounds (648648061091/50000000000000 : ℝ) j136.value (1297296122187/100000000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h460
  have j136_tangent : Bounds (2861135452357/100000000000000 : ℝ) j136.tangent (178820965773/6250000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h463
  let v464 : ℝ := j129.value*j52.value
  have h464 : Bounds (172301607469/20000000000000 : ℝ) v464 (430754018673/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v465 : ℝ := j129.tangent*j52.value
  have h465 : Bounds (190002201193/20000000000000 : ℝ) v465 (950011005967/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v466 : ℝ := j129.value*j52.tangent
  have h466 : Bounds (172301607469/20000000000000 : ℝ) v466 (430754018673/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v467 : ℝ := v465+v466
  have h467 : Bounds (181151904331/10000000000000 : ℝ) v467 (1811519043313/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h465 h466) (by norm_num) (by norm_num)
  obtain ⟨j137,hj137⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j52=z := ⟨_,rfl⟩
  have j137_value : Bounds (172301607469/20000000000000 : ℝ) j137.value (430754018673/50000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h464
  have j137_tangent : Bounds (181151904331/10000000000000 : ℝ) j137.tangent (1811519043313/100000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h467
  let v468 : ℝ := j133.value*j76.value
  have h468 : Bounds (54705760371447/50000000000000 : ℝ) v468 (109411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v469 : ℝ := j133.tangent*j76.value
  have h469 : Bounds (10378368977469/100000000000000 : ℝ) v469 (10378368977481/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v470 : ℝ := j133.value*j76.tangent
  have h470 : Bounds (54705760371447/50000000000000 : ℝ) v470 (109411520742903/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v471 : ℝ := v469+v470
  have h471 : Bounds (119789889720363/100000000000000 : ℝ) v471 (1871717026881/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h469 h470) (by norm_num) (by norm_num)
  obtain ⟨j138,hj138⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j76=z := ⟨_,rfl⟩
  have j138_value : Bounds (54705760371447/50000000000000 : ℝ) j138.value (109411520742903/100000000000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h468
  have j138_tangent : Bounds (119789889720363/100000000000000 : ℝ) j138.tangent (1871717026881/1562500000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h471
  let v472 : ℝ := j137.value+j138.value
  have h472 : Bounds (110273028780239/100000000000000 : ℝ) v472 (110273028780249/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_value j138_value) (by norm_num) (by norm_num)
  let v473 : ℝ := j137.tangent+j138.tangent
  have h473 : Bounds (121601408763673/100000000000000 : ℝ) v473 (121601408763697/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_tangent j138_tangent) (by norm_num) (by norm_num)
  obtain ⟨j139,hj139⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j137 j138=z := ⟨_,rfl⟩
  have j139_value : Bounds (110273028780239/100000000000000 : ℝ) j139.value (110273028780249/100000000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h472
  have j139_tangent : Bounds (121601408763673/100000000000000 : ℝ) j139.tangent (121601408763697/100000000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h473
  let v474 : ℝ := j139.value*j110.value
  have h474 : Bounds (16475660751737/20000000000000 : ℝ) v474 (82378303758713/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v475 : ℝ := j139.tangent*j110.value
  have h475 : Bounds (45420525306243/50000000000000 : ℝ) v475 (90841050612527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v476 : ℝ := j139.value*j110.tangent
  have h476 : Bounds (3907049396349/50000000000000 : ℝ) v476 (312563951709/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v477 : ℝ := v475+v476
  have h477 : Bounds (96342919341/97656250000 : ℝ) v477 (24663787351313/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h475 h476) (by norm_num) (by norm_num)
  obtain ⟨j140,hj140⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j110=z := ⟨_,rfl⟩
  have j140_value : Bounds (16475660751737/20000000000000 : ℝ) j140.value (82378303758713/100000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h474
  have j140_tangent : Bounds (96342919341/97656250000 : ℝ) j140.tangent (24663787351313/25000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h477
  let v478 : ℝ := j136.value+j140.value
  have h478 : Bounds (83675599880867/100000000000000 : ℝ) v478 (836755998809/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_value j140_value) (by norm_num) (by norm_num)
  let v479 : ℝ := j136.tangent+j140.tangent
  have h479 : Bounds (101516284857541/100000000000000 : ℝ) v479 (5075814242881/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_tangent j140_tangent) (by norm_num) (by norm_num)
  obtain ⟨j141,hj141⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j136 j140=z := ⟨_,rfl⟩
  have j141_value : Bounds (83675599880867/100000000000000 : ℝ) j141.value (836755998809/1000000000000 : ℝ) := by
    simpa only [← hj141,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h478
  have j141_tangent : Bounds (101516284857541/100000000000000 : ℝ) j141.tangent (5075814242881/5000000000000 : ℝ) := by
    simpa only [← hj141,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h479
  let v480 : ℝ := j89.value*j83.value
  have h480 : Bounds (127/65536 : ℝ) v480 (127/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v481 : ℝ := j89.tangent*j83.value
  have h481 : Bounds (127/65536 : ℝ) v481 (127/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v482 : ℝ := j89.value*j83.tangent
  have h482 : Bounds (-1/65536 : ℝ) v482 (-1/65536 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v483 : ℝ := v481+v482
  have h483 : Bounds (63/32768 : ℝ) v483 (63/32768 : ℝ) := by
    exact enlarge (IntervalBounds.add h481 h482) (by norm_num) (by norm_num)
  obtain ⟨j142,hj142⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j83=z := ⟨_,rfl⟩
  have j142_value : Bounds (127/65536 : ℝ) j142.value (127/65536 : ℝ) := by
    simpa only [← hj142,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h480
  have j142_tangent : Bounds (63/32768 : ℝ) j142.tangent (63/32768 : ℝ) := by
    simpa only [← hj142,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h483
  let v484 : ℝ := j92.value*j142.value
  have h484 : Bounds (648304547863/50000000000000 : ℝ) v484 (1296609095727/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v485 : ℝ := j92.tangent*j142.value
  have h485 : Bounds (133201025571/100000000000000 : ℝ) v485 (33300256393/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v486 : ℝ := j92.value*j142.tangent
  have h486 : Bounds (1286399575287/100000000000000 : ℝ) v486 (160799946911/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v487 : ℝ := v485+v486
  have h487 : Bounds (709800300429/50000000000000 : ℝ) v487 (70980030043/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h485 h486) (by norm_num) (by norm_num)
  obtain ⟨j143,hj143⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j142=z := ⟨_,rfl⟩
  have j143_value : Bounds (648304547863/50000000000000 : ℝ) j143.value (1296609095727/100000000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h484
  have j143_tangent : Bounds (709800300429/50000000000000 : ℝ) j143.tangent (70980030043/5000000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h487
  let v488 : ℝ := j141.value+j143.value
  have h488 : Bounds (84972208976593/100000000000000 : ℝ) v488 (84972208976627/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_value j143_value) (by norm_num) (by norm_num)
  let v489 : ℝ := j141.tangent+j143.tangent
  have h489 : Bounds (102935885458399/100000000000000 : ℝ) v489 (1286698568231/1250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_tangent j143_tangent) (by norm_num) (by norm_num)
  obtain ⟨j144,hj144⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j141 j143=z := ⟨_,rfl⟩
  have j144_value : Bounds (84972208976593/100000000000000 : ℝ) j144.value (84972208976627/100000000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h488
  have j144_tangent : Bounds (102935885458399/100000000000000 : ℝ) j144.tangent (1286698568231/1250000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h489
  let v490 : ℝ := j135.value*j118.value
  have h490 : Bounds (1900022011931/100000000000000 : ℝ) v490 (950011005967/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v491 : ℝ := j135.tangent*j118.value
  have h491 : Bounds (2095211820047/100000000000000 : ℝ) v491 (523802955013/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v492 : ℝ := j135.value*j118.tangent
  have h492 : Bounds (2095211820047/100000000000000 : ℝ) v492 (523802955013/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v493 : ℝ := v491+v492
  have h493 : Bounds (2095211820047/50000000000000 : ℝ) v493 (523802955013/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h491 h492) (by norm_num) (by norm_num)
  obtain ⟨j145,hj145⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j118=z := ⟨_,rfl⟩
  have j145_value : Bounds (1900022011931/100000000000000 : ℝ) j145.value (950011005967/50000000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h490
  have j145_tangent : Bounds (2095211820047/50000000000000 : ℝ) j145.tangent (523802955013/12500000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h493
  let v494 : ℝ := j139.value*j121.value
  have h494 : Bounds (30162849439427/25000000000000 : ℝ) v494 (12065139775773/10000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v495 : ℝ := j139.tangent*j121.value
  have h495 : Bounds (133045950573117/100000000000000 : ℝ) v495 (26609190114631/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v496 : ℝ := j139.value*j121.tangent
  have h496 : Bounds (11444541809443/100000000000000 : ℝ) v496 (11444541809459/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v497 : ℝ := v495+v496
  have h497 : Bounds (903065577391/625000000000 : ℝ) v497 (72245246191307/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h495 h496) (by norm_num) (by norm_num)
  obtain ⟨j146,hj146⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j121=z := ⟨_,rfl⟩
  have j146_value : Bounds (30162849439427/25000000000000 : ℝ) j146.value (12065139775773/10000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h494
  have j146_tangent : Bounds (903065577391/625000000000 : ℝ) j146.tangent (72245246191307/50000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h497
  let v498 : ℝ := j145.value+j146.value
  have h498 : Bounds (122551419769639/100000000000000 : ℝ) v498 (1914865933901/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_value j146_value) (by norm_num) (by norm_num)
  let v499 : ℝ := j145.tangent+j146.tangent
  have h499 : Bounds (74340458011327/50000000000000 : ℝ) v499 (74340458011359/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_tangent j146_tangent) (by norm_num) (by norm_num)
  obtain ⟨j147,hj147⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j145 j146=z := ⟨_,rfl⟩
  have j147_value : Bounds (122551419769639/100000000000000 : ℝ) j147.value (1914865933901/1562500000000 : ℝ) := by
    simpa only [← hj147,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h498
  have j147_tangent : Bounds (74340458011327/50000000000000 : ℝ) j147.tangent (74340458011359/50000000000000 : ℝ) := by
    simpa only [← hj147,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h499
  let v500 : ℝ := j89.value*j89.value
  have h500 : Bounds (1/4096 : ℝ) v500 (1/4096 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v501 : ℝ := j89.tangent*j89.value
  have h501 : Bounds (1/4096 : ℝ) v501 (1/4096 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v502 : ℝ := j89.value*j89.tangent
  have h502 : Bounds (1/4096 : ℝ) v502 (1/4096 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v503 : ℝ := v501+v502
  have h503 : Bounds (1/2048 : ℝ) v503 (1/2048 : ℝ) := by
    exact enlarge (IntervalBounds.add h501 h502) (by norm_num) (by norm_num)
  obtain ⟨j148,hj148⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j89=z := ⟨_,rfl⟩
  have j148_value : Bounds (1/4096 : ℝ) j148.value (1/4096 : ℝ) := by
    simpa only [← hj148,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h500
  have j148_tangent : Bounds (1/2048 : ℝ) j148.tangent (1/2048 : ℝ) := by
    simpa only [← hj148,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h503
  let v504 : ℝ := j92.value*j148.value
  have h504 : Bounds (8167616351/5000000000000 : ℝ) v504 (163352327021/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v505 : ℝ := j92.tangent*j148.value
  have h505 : Bounds (1048826973/6250000000000 : ℝ) v505 (16781231569/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v506 : ℝ := j92.value*j148.tangent
  have h506 : Bounds (326704654041/100000000000000 : ℝ) v506 (163352327021/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v507 : ℝ := v505+v506
  have h507 : Bounds (343485885609/100000000000000 : ℝ) v507 (343485885611/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h505 h506) (by norm_num) (by norm_num)
  obtain ⟨j149,hj149⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j148=z := ⟨_,rfl⟩
  have j149_value : Bounds (8167616351/5000000000000 : ℝ) j149.value (163352327021/100000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h504
  have j149_tangent : Bounds (343485885609/100000000000000 : ℝ) j149.tangent (343485885611/100000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h507
  let v508 : ℝ := j147.value+j149.value
  have h508 : Bounds (122714772096659/100000000000000 : ℝ) v508 (24542954419337/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_value j149_value) (by norm_num) (by norm_num)
  let v509 : ℝ := j147.tangent+j149.tangent
  have h509 : Bounds (149024401908263/100000000000000 : ℝ) v509 (149024401908329/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_tangent j149_tangent) (by norm_num) (by norm_num)
  obtain ⟨j150,hj150⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j147 j149=z := ⟨_,rfl⟩
  have j150_value : Bounds (122714772096659/100000000000000 : ℝ) j150.value (24542954419337/20000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h508
  have j150_tangent : Bounds (149024401908263/100000000000000 : ℝ) j150.tangent (149024401908329/100000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h509
  have hm12 : jetIter c d 1 2=!![j115,j126;j144,j150] := by
    rw [jetIter,hm11]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj79,← hj80,← hj81,← hj82,← hj83,← hj84,← hj85,← hj86,← hj87,← hj88,← hj89,← hj90,← hj91,← hj92,← hj93,← hj94,← hj95,← hj96,← hj97,← hj98,← hj99,← hj100,← hj101,← hj102,← hj103,← hj104,← hj105,← hj106,← hj107,← hj108,← hj109,← hj110,← hj111,← hj112,← hj113,← hj114,← hj115,← hj116,← hj117,← hj118,← hj119,← hj120,← hj121,← hj122,← hj123,← hj124,← hj125,← hj126,← hj127,← hj128,← hj129,← hj130,← hj131,← hj132,← hj133,← hj134,← hj135,← hj136,← hj137,← hj138,← hj139,← hj140,← hj141,← hj142,← hj143,← hj144,← hj145,← hj146,← hj147,← hj148,← hj149,← hj150]
    all_goals rfl
  let v510 : ℝ := -c
  have h510 : Bounds (-318481427627119/1000000000000000 : ℝ) v510 (-159240713813559/500000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hc) (by norm_num) (by norm_num)
  let v511 : ℝ := (1 : ℝ)+v510
  have h511 : Bounds (8518982154661/12500000000000 : ℝ) v511 (68151857237289/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (1 : ℝ)) h510) (by norm_num) (by norm_num)
  obtain ⟨j151,hj151⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((1 : ℝ)+(-c))=z := ⟨_,rfl⟩
  have j151_value : Bounds (8518982154661/12500000000000 : ℝ) j151.value (68151857237289/100000000000000 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h511
  have j151_tangent : Bounds (0 : ℝ) j151.tangent (0 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j152,hj152⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/16 : ℝ)=z := ⟨_,rfl⟩
  have j152_value : Bounds (-1/16 : ℝ) j152.value (-1/16 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/16 : ℝ))
  have j152_tangent : Bounds (0 : ℝ) j152.tangent (0 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j153,hj153⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant c=z := ⟨_,rfl⟩
  have j153_value : Bounds (159240713813559/500000000000000 : ℝ) j153.value (318481427627119/1000000000000000 : ℝ) := by
    convert hc using 1 <;> norm_num [← hj153,LReturnJets.constant]
  have j153_tangent : Bounds (0 : ℝ) j153.tangent (0 : ℝ) := by
    simpa only [← hj153,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v512 : ℝ := j115.value*j153.value
  have h512 : Bounds (335519292431/1562500000000 : ℝ) v512 (21473234715597/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v513 : ℝ := j115.tangent*j153.value
  have h513 : Bounds (22360086595053/100000000000000 : ℝ) v513 (559002164877/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v514 : ℝ := j115.value*j153.tangent
  have h514 : Bounds (0 : ℝ) v514 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v515 : ℝ := v513+v514
  have h515 : Bounds (22360086595053/100000000000000 : ℝ) v515 (559002164877/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h513 h514) (by norm_num) (by norm_num)
  obtain ⟨j154,hj154⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j115 j153=z := ⟨_,rfl⟩
  have j154_value : Bounds (335519292431/1562500000000 : ℝ) j154.value (21473234715597/100000000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h512
  have j154_tangent : Bounds (22360086595053/100000000000000 : ℝ) j154.tangent (559002164877/2500000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h515
  obtain ⟨j155,hj155⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant d=z := ⟨_,rfl⟩
  have j155_value : Bounds (-1025232119675749/1000000000000000 : ℝ) j155.value (-256308029918937/250000000000000 : ℝ) := by
    convert hd using 1 <;> norm_num [← hj155,LReturnJets.constant]
  have j155_tangent : Bounds (0 : ℝ) j155.tangent (0 : ℝ) := by
    simpa only [← hj155,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v516 : ℝ := j126.value*j155.value
  have h516 : Bounds (-87116237922639/100000000000000 : ℝ) v516 (-43558118961301/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v517 : ℝ := j126.tangent*j155.value
  have h517 : Bounds (-1055331760393/1000000000000 : ℝ) v517 (-52766588019607/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v518 : ℝ := j126.value*j155.tangent
  have h518 : Bounds (0 : ℝ) v518 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j126_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v519 : ℝ := v517+v518
  have h519 : Bounds (-1055331760393/1000000000000 : ℝ) v519 (-52766588019607/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h517 h518) (by norm_num) (by norm_num)
  obtain ⟨j156,hj156⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j126 j155=z := ⟨_,rfl⟩
  have j156_value : Bounds (-87116237922639/100000000000000 : ℝ) j156.value (-43558118961301/50000000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h516
  have j156_tangent : Bounds (-1055331760393/1000000000000 : ℝ) j156.tangent (-52766588019607/50000000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h519
  let v520 : ℝ := j154.value+j156.value
  have h520 : Bounds (-13128600641411/20000000000000 : ℝ) v520 (-13128600641401/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_value j156_value) (by norm_num) (by norm_num)
  let v521 : ℝ := j154.tangent+j156.tangent
  have h521 : Bounds (-83173089444247/100000000000000 : ℝ) v521 (-41586544722067/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_tangent j156_tangent) (by norm_num) (by norm_num)
  obtain ⟨j157,hj157⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j154 j156=z := ⟨_,rfl⟩
  have j157_value : Bounds (-13128600641411/20000000000000 : ℝ) j157.value (-13128600641401/20000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h520
  have j157_tangent : Bounds (-83173089444247/100000000000000 : ℝ) j157.tangent (-41586544722067/50000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h521
  let v522 : ℝ := j152.value*j157.value
  have h522 : Bounds (4102687700437/100000000000000 : ℝ) v522 (4102687700441/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v523 : ℝ := j152.tangent*j157.value
  have h523 : Bounds (0 : ℝ) v523 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v524 : ℝ := j152.value*j157.tangent
  have h524 : Bounds (2599159045129/50000000000000 : ℝ) v524 (2599159045133/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v525 : ℝ := v523+v524
  have h525 : Bounds (2599159045129/50000000000000 : ℝ) v525 (2599159045133/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h523 h524) (by norm_num) (by norm_num)
  obtain ⟨j158,hj158⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j157=z := ⟨_,rfl⟩
  have j158_value : Bounds (4102687700437/100000000000000 : ℝ) j158.value (4102687700441/100000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h522
  have j158_tangent : Bounds (2599159045129/50000000000000 : ℝ) j158.tangent (2599159045133/50000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h525
  let v526 : ℝ := j151.value*j158.value
  have h526 : Bounds (2796057864493/100000000000000 : ℝ) v526 (2796057864497/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v527 : ℝ := j151.tangent*j158.value
  have h527 : Bounds (0 : ℝ) v527 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v528 : ℝ := j151.value*j158.tangent
  have h528 : Bounds (885687580903/25000000000000 : ℝ) v528 (3542750323619/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v529 : ℝ := v527+v528
  have h529 : Bounds (885687580903/25000000000000 : ℝ) v529 (3542750323619/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h527 h528) (by norm_num) (by norm_num)
  obtain ⟨j159,hj159⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j158=z := ⟨_,rfl⟩
  have j159_value : Bounds (2796057864493/100000000000000 : ℝ) j159.value (2796057864497/100000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h526
  have j159_tangent : Bounds (885687580903/25000000000000 : ℝ) j159.tangent (3542750323619/100000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h529
  let v530 : ℝ := -d
  have h530 : Bounds (256308029918937/250000000000000 : ℝ) v530 (1025232119675749/1000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hd) (by norm_num) (by norm_num)
  let v531 : ℝ := (0 : ℝ)+v530
  have h531 : Bounds (51261605983787/50000000000000 : ℝ) v531 (4100928478703/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (0 : ℝ)) h530) (by norm_num) (by norm_num)
  obtain ⟨j160,hj160⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((0 : ℝ)+(-d))=z := ⟨_,rfl⟩
  have j160_value : Bounds (51261605983787/50000000000000 : ℝ) j160.value (4100928478703/4000000000000 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h531
  have j160_tangent : Bounds (0 : ℝ) j160.tangent (0 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v532 : ℝ := j144.value*j153.value
  have h532 : Bounds (5412414084699/20000000000000 : ℝ) v532 (27062070423507/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v533 : ℝ := j144.tangent*j153.value
  have h533 : Bounds (8195791938713/25000000000000 : ℝ) v533 (32783167754879/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v534 : ℝ := j144.value*j153.tangent
  have h534 : Bounds (0 : ℝ) v534 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v535 : ℝ := v533+v534
  have h535 : Bounds (8195791938713/25000000000000 : ℝ) v535 (32783167754879/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h533 h534) (by norm_num) (by norm_num)
  obtain ⟨j161,hj161⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j144 j153=z := ⟨_,rfl⟩
  have j161_value : Bounds (5412414084699/20000000000000 : ℝ) j161.value (27062070423507/100000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h532
  have j161_tangent : Bounds (8195791938713/25000000000000 : ℝ) j161.tangent (32783167754879/100000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h535
  let v536 : ℝ := j150.value*j155.value
  have h536 : Bounds (-125811125912211/100000000000000 : ℝ) v536 (-15726390739023/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v537 : ℝ := j150.tangent*j155.value
  have h537 : Bounds (-152784603451887/100000000000000 : ℝ) v537 (-152784603451819/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v538 : ℝ := j150.value*j155.tangent
  have h538 : Bounds (0 : ℝ) v538 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j150_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v539 : ℝ := v537+v538
  have h539 : Bounds (-152784603451887/100000000000000 : ℝ) v539 (-152784603451819/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h537 h538) (by norm_num) (by norm_num)
  obtain ⟨j162,hj162⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j150 j155=z := ⟨_,rfl⟩
  have j162_value : Bounds (-125811125912211/100000000000000 : ℝ) j162.value (-15726390739023/12500000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h536
  have j162_tangent : Bounds (-152784603451887/100000000000000 : ℝ) j162.tangent (-152784603451819/100000000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h539
  let v540 : ℝ := j161.value+j162.value
  have h540 : Bounds (-24687263872179/25000000000000 : ℝ) v540 (-98749055488677/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_value j162_value) (by norm_num) (by norm_num)
  let v541 : ℝ := j161.tangent+j162.tangent
  have h541 : Bounds (-24000287139407/20000000000000 : ℝ) v541 (-6000071784847/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_tangent j162_tangent) (by norm_num) (by norm_num)
  obtain ⟨j163,hj163⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j161 j162=z := ⟨_,rfl⟩
  have j163_value : Bounds (-24687263872179/25000000000000 : ℝ) j163.value (-98749055488677/100000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h540
  have j163_tangent : Bounds (-24000287139407/20000000000000 : ℝ) j163.tangent (-6000071784847/5000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h541
  let v542 : ℝ := j152.value*j163.value
  have h542 : Bounds (3085907984021/50000000000000 : ℝ) v542 (1234363193609/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v543 : ℝ := j152.tangent*j163.value
  have h543 : Bounds (0 : ℝ) v543 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v544 : ℝ := j152.value*j163.tangent
  have h544 : Bounds (3750044865529/50000000000000 : ℝ) v544 (1500017946213/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v545 : ℝ := v543+v544
  have h545 : Bounds (3750044865529/50000000000000 : ℝ) v545 (1500017946213/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h543 h544) (by norm_num) (by norm_num)
  obtain ⟨j164,hj164⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j163=z := ⟨_,rfl⟩
  have j164_value : Bounds (3085907984021/50000000000000 : ℝ) j164.value (1234363193609/20000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h542
  have j164_tangent : Bounds (3750044865529/50000000000000 : ℝ) j164.tangent (1500017946213/20000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h545
  let v546 : ℝ := j160.value*j164.value
  have h546 : Bounds (1581885991791/25000000000000 : ℝ) v546 (98867874487/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v547 : ℝ := j160.tangent*j164.value
  have h547 : Bounds (0 : ℝ) v547 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v548 : ℝ := j160.value*j164.tangent
  have h548 : Bounds (768933289273/10000000000000 : ℝ) v548 (7689332892739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v549 : ℝ := v547+v548
  have h549 : Bounds (768933289273/10000000000000 : ℝ) v549 (7689332892739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h547 h548) (by norm_num) (by norm_num)
  obtain ⟨j165,hj165⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j164=z := ⟨_,rfl⟩
  have j165_value : Bounds (1581885991791/25000000000000 : ℝ) j165.value (98867874487/1562500000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h546
  have j165_tangent : Bounds (768933289273/10000000000000 : ℝ) j165.tangent (7689332892739/100000000000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h549
  let v550 : ℝ := j159.value+j165.value
  have h550 : Bounds (9123601831657/100000000000000 : ℝ) v550 (1824720366333/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_value j165_value) (by norm_num) (by norm_num)
  let v551 : ℝ := j159.tangent+j165.tangent
  have h551 : Bounds (5616041608171/50000000000000 : ℝ) v551 (5616041608179/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_tangent j165_tangent) (by norm_num) (by norm_num)
  obtain ⟨j166,hj166⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j159 j165=z := ⟨_,rfl⟩
  have j166_value : Bounds (9123601831657/100000000000000 : ℝ) j166.value (1824720366333/20000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h550
  have j166_tangent : Bounds (5616041608171/50000000000000 : ℝ) j166.tangent (5616041608179/50000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h551
  let v552 : ℝ := j166.value⁻¹
  have h552 : Bounds (274014588331039/25000000000000 : ℝ) v552 (548029176662559/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j166_value (by norm_num)) (by norm_num) (by norm_num)
  let v553 : ℝ := -j166.tangent
  have h553 : Bounds (-5616041608179/50000000000000 : ℝ) v553 (-5616041608171/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j166_tangent) (by norm_num) (by norm_num)
  let v554 : ℝ := j166.value*j166.value
  have h554 : Bounds (416200551913/50000000000000 : ℝ) v554 (208100275957/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j166_value j166_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v555 : ℝ := v554⁻¹
  have h555 : Bounds (6006719569455491/50000000000000 : ℝ) v555 (1501679892367481/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h554 (by norm_num)) (by norm_num) (by norm_num)
  let v556 : ℝ := v553*v555
  have h556 : Bounds (-674679740616123/50000000000000 : ℝ) v556 (-1349359481227081/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn h553 h555 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j167,hj167⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j166=z := ⟨_,rfl⟩
  have j167_value : Bounds (274014588331039/25000000000000 : ℝ) j167.value (548029176662559/50000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h552
  have j167_tangent : Bounds (-674679740616123/50000000000000 : ℝ) j167.tangent (-1349359481227081/100000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h556
  let v557 : ℝ := j158.value*j151.value
  have h557 : Bounds (2796057864493/100000000000000 : ℝ) v557 (2796057864497/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v558 : ℝ := j158.tangent*j151.value
  have h558 : Bounds (885687580903/25000000000000 : ℝ) v558 (3542750323619/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v559 : ℝ := j158.value*j151.tangent
  have h559 : Bounds (0 : ℝ) v559 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v560 : ℝ := v558+v559
  have h560 : Bounds (885687580903/25000000000000 : ℝ) v560 (3542750323619/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h558 h559) (by norm_num) (by norm_num)
  obtain ⟨j168,hj168⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j151=z := ⟨_,rfl⟩
  have j168_value : Bounds (2796057864493/100000000000000 : ℝ) j168.value (2796057864497/100000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h557
  have j168_tangent : Bounds (885687580903/25000000000000 : ℝ) j168.tangent (3542750323619/100000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h560
  let v561 : ℝ := j167.value*j168.value
  have h561 : Bounds (957700805861/3125000000000 : ℝ) v561 (3830803223453/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v562 : ℝ := j167.tangent*j168.value
  have h562 : Bounds (-37728871895331/100000000000000 : ℝ) v562 (-37728871895131/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v563 : ℝ := j167.value*j168.tangent
  have h563 : Bounds (38830610859367/100000000000000 : ℝ) v563 (38830610859479/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v564 : ℝ := v562+v563
  have h564 : Bounds (275434741009/25000000000000 : ℝ) v564 (275434741087/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h562 h563) (by norm_num) (by norm_num)
  obtain ⟨j169,hj169⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j168=z := ⟨_,rfl⟩
  have j169_value : Bounds (957700805861/3125000000000 : ℝ) j169.value (3830803223453/12500000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h561
  have j169_tangent : Bounds (275434741009/25000000000000 : ℝ) j169.tangent (275434741087/25000000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h564
  let v565 : ℝ := -j169.value
  have h565 : Bounds (-3830803223453/12500000000000 : ℝ) v565 (-957700805861/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_value) (by norm_num) (by norm_num)
  let v566 : ℝ := j0.value+v565
  have h566 : Bounds (8669196776547/12500000000000 : ℝ) v566 (2167299194139/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h565) (by norm_num) (by norm_num)
  let v567 : ℝ := -j169.tangent
  have h567 : Bounds (-275434741087/25000000000000 : ℝ) v567 (-275434741009/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_tangent) (by norm_num) (by norm_num)
  let v568 : ℝ := j0.tangent+v567
  have h568 : Bounds (-275434741087/25000000000000 : ℝ) v568 (-275434741009/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h567) (by norm_num) (by norm_num)
  obtain ⟨j170,hj170⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j169=z := ⟨_,rfl⟩
  have j170_value : Bounds (8669196776547/12500000000000 : ℝ) j170.value (2167299194139/3125000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h566
  have j170_tangent : Bounds (-275434741087/25000000000000 : ℝ) j170.tangent (-275434741009/25000000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h568
  let v569 : ℝ := j170.value*j115.value
  have h569 : Bounds (23380414809787/50000000000000 : ℝ) v569 (46760829619649/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v570 : ℝ := j170.tangent*j115.value
  have h570 : Bounds (-46427156587/6250000000000 : ℝ) v570 (-37141725259/5000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v571 : ℝ := j170.value*j115.tangent
  have h571 : Bounds (24346033874239/50000000000000 : ℝ) v571 (12173016937147/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v572 : ℝ := v570+v571
  have h572 : Bounds (23974616621543/50000000000000 : ℝ) v572 (2996827077713/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h570 h571) (by norm_num) (by norm_num)
  obtain ⟨j171,hj171⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j115=z := ⟨_,rfl⟩
  have j171_value : Bounds (23380414809787/50000000000000 : ℝ) j171.value (46760829619649/100000000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h569
  have j171_tangent : Bounds (23974616621543/50000000000000 : ℝ) j171.tangent (2996827077713/6250000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h572
  let v573 : ℝ := j158.value*j160.value
  have h573 : Bounds (2103103603743/50000000000000 : ℝ) v573 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v574 : ℝ := j158.tangent*j160.value
  have h574 : Bounds (5329482674423/100000000000000 : ℝ) v574 (5329482674433/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v575 : ℝ := j158.value*j160.tangent
  have h575 : Bounds (0 : ℝ) v575 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v576 : ℝ := v574+v575
  have h576 : Bounds (5329482674423/100000000000000 : ℝ) v576 (5329482674433/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h574 h575) (by norm_num) (by norm_num)
  obtain ⟨j172,hj172⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j160=z := ⟨_,rfl⟩
  have j172_value : Bounds (2103103603743/50000000000000 : ℝ) j172.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h573
  have j172_tangent : Bounds (5329482674423/100000000000000 : ℝ) j172.tangent (5329482674433/100000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h576
  let v577 : ℝ := j167.value*j172.value
  have h577 : Bounds (46102485455773/100000000000000 : ℝ) v577 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v578 : ℝ := j167.tangent*j172.value
  have h578 : Bounds (-28378427877277/50000000000000 : ℝ) v578 (-56756855754269/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v579 : ℝ := j167.value*j172.tangent
  have h579 : Bounds (7301780005247/12500000000000 : ℝ) v579 (29207120021069/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v580 : ℝ := v578+v579
  have h580 : Bounds (828692143711/50000000000000 : ℝ) v580 (1657384287869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h578 h579) (by norm_num) (by norm_num)
  obtain ⟨j173,hj173⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j172=z := ⟨_,rfl⟩
  have j173_value : Bounds (46102485455773/100000000000000 : ℝ) j173.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h577
  have j173_tangent : Bounds (828692143711/50000000000000 : ℝ) j173.tangent (1657384287869/100000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h580
  let v581 : ℝ := -j173.value
  have h581 : Bounds (-46102485455869/100000000000000 : ℝ) v581 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_value) (by norm_num) (by norm_num)
  let v582 : ℝ := j6.value+v581
  have h582 : Bounds (-46102485455869/100000000000000 : ℝ) v582 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h581) (by norm_num) (by norm_num)
  let v583 : ℝ := -j173.tangent
  have h583 : Bounds (-1657384287869/100000000000000 : ℝ) v583 (-828692143711/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_tangent) (by norm_num) (by norm_num)
  let v584 : ℝ := j6.tangent+v583
  have h584 : Bounds (-1657384287869/100000000000000 : ℝ) v584 (-828692143711/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h583) (by norm_num) (by norm_num)
  obtain ⟨j174,hj174⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j173=z := ⟨_,rfl⟩
  have j174_value : Bounds (-46102485455869/100000000000000 : ℝ) j174.value (-46102485455773/100000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h582
  have j174_tangent : Bounds (-1657384287869/100000000000000 : ℝ) j174.tangent (-828692143711/50000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h584
  let v585 : ℝ := j174.value*j144.value
  have h585 : Bounds (-39174300284981/100000000000000 : ℝ) v585 (-19587150142441/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v586 : ℝ := j174.tangent*j144.value
  have h586 : Bounds (-704158020317/50000000000000 : ℝ) v586 (-1408316040253/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v587 : ℝ := j174.value*j144.tangent
  have h587 : Bounds (-23728000811183/50000000000000 : ℝ) v587 (-47456001622229/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v588 : ℝ := v586+v587
  have h588 : Bounds (-48864317663/100000000000 : ℝ) v588 (-24432158831241/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h586 h587) (by norm_num) (by norm_num)
  obtain ⟨j175,hj175⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j144=z := ⟨_,rfl⟩
  have j175_value : Bounds (-39174300284981/100000000000000 : ℝ) j175.value (-19587150142441/50000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h585
  have j175_tangent : Bounds (-48864317663/100000000000 : ℝ) j175.tangent (-24432158831241/50000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h588
  let v589 : ℝ := j171.value+j175.value
  have h589 : Bounds (7586529334593/100000000000000 : ℝ) v589 (7586529334767/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_value j175_value) (by norm_num) (by norm_num)
  let v590 : ℝ := j171.tangent+j175.tangent
  have h590 : Bounds (-457542209957/50000000000000 : ℝ) v590 (-457542209537/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_tangent j175_tangent) (by norm_num) (by norm_num)
  obtain ⟨j176,hj176⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j171 j175=z := ⟨_,rfl⟩
  have j176_value : Bounds (7586529334593/100000000000000 : ℝ) j176.value (7586529334767/100000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h589
  have j176_tangent : Bounds (-457542209957/50000000000000 : ℝ) j176.tangent (-457542209537/50000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h590
  let v591 : ℝ := j167.value*j159.value
  have h591 : Bounds (957700805861/3125000000000 : ℝ) v591 (3830803223453/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v592 : ℝ := j167.tangent*j159.value
  have h592 : Bounds (-37728871895331/100000000000000 : ℝ) v592 (-37728871895131/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v593 : ℝ := j167.value*j159.tangent
  have h593 : Bounds (38830610859367/100000000000000 : ℝ) v593 (38830610859479/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v594 : ℝ := v592+v593
  have h594 : Bounds (275434741009/25000000000000 : ℝ) v594 (275434741087/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h592 h593) (by norm_num) (by norm_num)
  obtain ⟨j177,hj177⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j159=z := ⟨_,rfl⟩
  have j177_value : Bounds (957700805861/3125000000000 : ℝ) j177.value (3830803223453/12500000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h591
  have j177_tangent : Bounds (275434741009/25000000000000 : ℝ) j177.tangent (275434741087/25000000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h594
  let v595 : ℝ := -j177.value
  have h595 : Bounds (-3830803223453/12500000000000 : ℝ) v595 (-957700805861/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_value) (by norm_num) (by norm_num)
  let v596 : ℝ := j0.value+v595
  have h596 : Bounds (8669196776547/12500000000000 : ℝ) v596 (2167299194139/3125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h595) (by norm_num) (by norm_num)
  let v597 : ℝ := -j177.tangent
  have h597 : Bounds (-275434741087/25000000000000 : ℝ) v597 (-275434741009/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_tangent) (by norm_num) (by norm_num)
  let v598 : ℝ := j0.tangent+v597
  have h598 : Bounds (-275434741087/25000000000000 : ℝ) v598 (-275434741009/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h597) (by norm_num) (by norm_num)
  obtain ⟨j178,hj178⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j177=z := ⟨_,rfl⟩
  have j178_value : Bounds (8669196776547/12500000000000 : ℝ) j178.value (2167299194139/3125000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h596
  have j178_tangent : Bounds (-275434741087/25000000000000 : ℝ) j178.tangent (-275434741009/25000000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h598
  let v599 : ℝ := j176.value*j178.value
  have h599 : Bounds (526152925221/10000000000000 : ℝ) v599 (5261529252337/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v600 : ℝ := j176.tangent*j178.value
  have h600 : Bounds (-39665234517/6250000000000 : ℝ) v600 (-79330468961/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j176_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v601 : ℝ := j176.value*j178.tangent
  have h601 : Bounds (-83583749723/100000000000000 : ℝ) v601 (-83583749697/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v602 : ℝ := v600+v601
  have h602 : Bounds (-143645500399/20000000000000 : ℝ) v602 (-143645500277/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h600 h601) (by norm_num) (by norm_num)
  obtain ⟨j179,hj179⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j178=z := ⟨_,rfl⟩
  have j179_value : Bounds (526152925221/10000000000000 : ℝ) j179.value (5261529252337/100000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h599
  have j179_tangent : Bounds (-143645500399/20000000000000 : ℝ) j179.tangent (-143645500277/20000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h602
  let v603 : ℝ := j170.value*j126.value
  have h603 : Bounds (2357250560499/4000000000000 : ℝ) v603 (29465632006281/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v604 : ℝ := j170.tangent*j126.value
  have h604 : Bounds (-936171935163/100000000000000 : ℝ) v604 (-936171934897/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v605 : ℝ := j170.value*j126.tangent
  have h605 : Bounds (71389715712557/100000000000000 : ℝ) v605 (71389715712689/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v606 : ℝ := v604+v605
  have h606 : Bounds (35226771888697/50000000000000 : ℝ) v606 (137604577691/195312500000 : ℝ) := by
    exact enlarge (IntervalBounds.add h604 h605) (by norm_num) (by norm_num)
  obtain ⟨j180,hj180⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j126=z := ⟨_,rfl⟩
  have j180_value : Bounds (2357250560499/4000000000000 : ℝ) j180.value (29465632006281/50000000000000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h603
  have j180_tangent : Bounds (35226771888697/50000000000000 : ℝ) j180.tangent (137604577691/195312500000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h606
  let v607 : ℝ := j174.value*j150.value
  have h607 : Bounds (-56574559958077/100000000000000 : ℝ) v607 (-56574559957947/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v608 : ℝ := j174.tangent*j150.value
  have h608 : Bounds (-16270842813/800000000000 : ℝ) v608 (-81354214043/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v609 : ℝ := j174.value*j150.tangent
  have h609 : Bounds (-17175988303871/25000000000000 : ℝ) v609 (-68703953215309/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v610 : ℝ := v608+v609
  have h610 : Bounds (-70737808567109/100000000000000 : ℝ) v610 (-4421113035399/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h608 h609) (by norm_num) (by norm_num)
  obtain ⟨j181,hj181⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j150=z := ⟨_,rfl⟩
  have j181_value : Bounds (-56574559958077/100000000000000 : ℝ) j181.value (-56574559957947/100000000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h607
  have j181_tangent : Bounds (-70737808567109/100000000000000 : ℝ) j181.tangent (-4421113035399/6250000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h610
  let v611 : ℝ := j180.value+j181.value
  have h611 : Bounds (1178352027199/50000000000000 : ℝ) v611 (471340810923/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_value j181_value) (by norm_num) (by norm_num)
  let v612 : ℝ := j180.tangent+j181.tangent
  have h612 : Bounds (-56852957943/20000000000000 : ℝ) v612 (-17766549287/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_tangent j181_tangent) (by norm_num) (by norm_num)
  obtain ⟨j182,hj182⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j180 j181=z := ⟨_,rfl⟩
  have j182_value : Bounds (1178352027199/50000000000000 : ℝ) j182.value (471340810923/20000000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h611
  have j182_tangent : Bounds (-56852957943/20000000000000 : ℝ) j182.tangent (-17766549287/6250000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h612
  let v613 : ℝ := j160.value*j158.value
  have h613 : Bounds (2103103603743/50000000000000 : ℝ) v613 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v614 : ℝ := j160.tangent*j158.value
  have h614 : Bounds (0 : ℝ) v614 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v615 : ℝ := j160.value*j158.tangent
  have h615 : Bounds (5329482674423/100000000000000 : ℝ) v615 (5329482674433/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v616 : ℝ := v614+v615
  have h616 : Bounds (5329482674423/100000000000000 : ℝ) v616 (5329482674433/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h614 h615) (by norm_num) (by norm_num)
  obtain ⟨j183,hj183⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j158=z := ⟨_,rfl⟩
  have j183_value : Bounds (2103103603743/50000000000000 : ℝ) j183.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h613
  have j183_tangent : Bounds (5329482674423/100000000000000 : ℝ) j183.tangent (5329482674433/100000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h616
  let v617 : ℝ := j167.value*j183.value
  have h617 : Bounds (46102485455773/100000000000000 : ℝ) v617 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v618 : ℝ := j167.tangent*j183.value
  have h618 : Bounds (-28378427877277/50000000000000 : ℝ) v618 (-56756855754269/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v619 : ℝ := j167.value*j183.tangent
  have h619 : Bounds (7301780005247/12500000000000 : ℝ) v619 (29207120021069/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v620 : ℝ := v618+v619
  have h620 : Bounds (828692143711/50000000000000 : ℝ) v620 (1657384287869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h618 h619) (by norm_num) (by norm_num)
  obtain ⟨j184,hj184⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j183=z := ⟨_,rfl⟩
  have j184_value : Bounds (46102485455773/100000000000000 : ℝ) j184.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h617
  have j184_tangent : Bounds (828692143711/50000000000000 : ℝ) j184.tangent (1657384287869/100000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h620
  let v621 : ℝ := -j184.value
  have h621 : Bounds (-46102485455869/100000000000000 : ℝ) v621 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_value) (by norm_num) (by norm_num)
  let v622 : ℝ := j6.value+v621
  have h622 : Bounds (-46102485455869/100000000000000 : ℝ) v622 (-46102485455773/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h621) (by norm_num) (by norm_num)
  let v623 : ℝ := -j184.tangent
  have h623 : Bounds (-1657384287869/100000000000000 : ℝ) v623 (-828692143711/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_tangent) (by norm_num) (by norm_num)
  let v624 : ℝ := j6.tangent+v623
  have h624 : Bounds (-1657384287869/100000000000000 : ℝ) v624 (-828692143711/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h623) (by norm_num) (by norm_num)
  obtain ⟨j185,hj185⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j184=z := ⟨_,rfl⟩
  have j185_value : Bounds (-46102485455869/100000000000000 : ℝ) j185.value (-46102485455773/100000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h622
  have j185_tangent : Bounds (-1657384287869/100000000000000 : ℝ) j185.tangent (-828692143711/50000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h624
  let v625 : ℝ := j182.value*j185.value
  have h625 : Bounds (-1086499144017/100000000000000 : ℝ) v625 (-543249571957/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v626 : ℝ := j182.tangent*j185.value
  have h626 : Bounds (8190820801/6250000000000 : ℝ) v626 (26210626667/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j182_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v627 : ℝ := j182.value*j185.tangent
  have h627 : Bounds (-39059642713/100000000000000 : ℝ) v627 (-19529821349/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v628 : ℝ := v626+v627
  have h628 : Bounds (91993490103/100000000000000 : ℝ) v628 (91993490637/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h626 h627) (by norm_num) (by norm_num)
  obtain ⟨j186,hj186⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j185=z := ⟨_,rfl⟩
  have j186_value : Bounds (-1086499144017/100000000000000 : ℝ) j186.value (-543249571957/50000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h625
  have j186_tangent : Bounds (91993490103/100000000000000 : ℝ) j186.tangent (91993490637/100000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h628
  let v629 : ℝ := j179.value+j186.value
  have h629 : Bounds (4175030108193/100000000000000 : ℝ) v629 (4175030108423/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_value j186_value) (by norm_num) (by norm_num)
  let v630 : ℝ := j179.tangent+j186.tangent
  have h630 : Bounds (-156558502973/25000000000000 : ℝ) v630 (-156558502687/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_tangent j186_tangent) (by norm_num) (by norm_num)
  obtain ⟨j187,hj187⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j179 j186=z := ⟨_,rfl⟩
  have j187_value : Bounds (4175030108193/100000000000000 : ℝ) j187.value (4175030108423/100000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h629
  have j187_tangent : Bounds (-156558502973/25000000000000 : ℝ) j187.tangent (-156558502687/25000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h630
  let v631 : ℝ := j158.value*j158.value
  have h631 : Bounds (168320463673/100000000000000 : ℝ) v631 (84160231837/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v632 : ℝ := j158.tangent*j158.value
  have h632 : Bounds (106635378459/50000000000000 : ℝ) v632 (5331768923/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v633 : ℝ := j158.value*j158.tangent
  have h633 : Bounds (106635378459/50000000000000 : ℝ) v633 (5331768923/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v634 : ℝ := v632+v633
  have h634 : Bounds (106635378459/25000000000000 : ℝ) v634 (5331768923/1250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h632 h633) (by norm_num) (by norm_num)
  obtain ⟨j188,hj188⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j158=z := ⟨_,rfl⟩
  have j188_value : Bounds (168320463673/100000000000000 : ℝ) j188.value (84160231837/50000000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h631
  have j188_tangent : Bounds (106635378459/25000000000000 : ℝ) j188.tangent (5331768923/1250000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h634
  let v635 : ℝ := j167.value*j188.value
  have h635 : Bounds (1844890502441/100000000000000 : ℝ) v635 (368978100491/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v636 : ℝ := j167.tangent*j188.value
  have h636 : Bounds (-28390601693/1250000000000 : ℝ) v636 (-2271248135417/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v637 : ℝ := j167.value*j188.tangent
  have h637 : Bounds (2337571946397/50000000000000 : ℝ) v637 (4675143892843/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v638 : ℝ := v636+v637
  have h638 : Bounds (1201947878677/50000000000000 : ℝ) v638 (1201947878713/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h636 h637) (by norm_num) (by norm_num)
  obtain ⟨j189,hj189⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j188=z := ⟨_,rfl⟩
  have j189_value : Bounds (1844890502441/100000000000000 : ℝ) j189.value (368978100491/20000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h635
  have j189_tangent : Bounds (1201947878677/50000000000000 : ℝ) j189.tangent (1201947878713/50000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h638
  let v639 : ℝ := j187.value+j189.value
  have h639 : Bounds (3009960305317/50000000000000 : ℝ) v639 (3009960305439/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_value j189_value) (by norm_num) (by norm_num)
  let v640 : ℝ := j187.tangent+j189.tangent
  have h640 : Bounds (888830872731/50000000000000 : ℝ) v640 (888830873339/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_tangent j189_tangent) (by norm_num) (by norm_num)
  obtain ⟨j190,hj190⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j187 j189=z := ⟨_,rfl⟩
  have j190_value : Bounds (3009960305317/50000000000000 : ℝ) j190.value (3009960305439/50000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h639
  have j190_tangent : Bounds (888830872731/50000000000000 : ℝ) j190.tangent (888830873339/50000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h640
  let v641 : ℝ := j151.value*j164.value
  have h641 : Bounds (65721987617/1562500000000 : ℝ) v641 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v642 : ℝ := j151.tangent*j164.value
  have h642 : Bounds (0 : ℝ) v642 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v643 : ℝ := j151.value*j164.tangent
  have h643 : Bounds (5111450446179/100000000000000 : ℝ) v643 (638931305773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v644 : ℝ := v642+v643
  have h644 : Bounds (5111450446179/100000000000000 : ℝ) v644 (638931305773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h642 h643) (by norm_num) (by norm_num)
  obtain ⟨j191,hj191⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j164=z := ⟨_,rfl⟩
  have j191_value : Bounds (65721987617/1562500000000 : ℝ) j191.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h641
  have j191_tangent : Bounds (5111450446179/100000000000000 : ℝ) j191.tangent (638931305773/12500000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h644
  let v645 : ℝ := j167.value*j191.value
  have h645 : Bounds (23051242727897/50000000000000 : ℝ) v645 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v646 : ℝ := j167.tangent*j191.value
  have h646 : Bounds (-28378427877277/50000000000000 : ℝ) v646 (-7094606969287/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v647 : ℝ := j167.value*j191.tangent
  have h647 : Bounds (56024479591369/100000000000000 : ℝ) v647 (28012239795737/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v648 : ℝ := v646+v647
  have h648 : Bounds (-146475232637/20000000000000 : ℝ) v648 (-366188081411/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h646 h647) (by norm_num) (by norm_num)
  obtain ⟨j192,hj192⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j191=z := ⟨_,rfl⟩
  have j192_value : Bounds (23051242727897/50000000000000 : ℝ) j192.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h645
  have j192_tangent : Bounds (-146475232637/20000000000000 : ℝ) j192.tangent (-366188081411/50000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h648
  let v649 : ℝ := -j192.value
  have h649 : Bounds (-46102485455869/100000000000000 : ℝ) v649 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_value) (by norm_num) (by norm_num)
  let v650 : ℝ := j6.value+v649
  have h650 : Bounds (-46102485455869/100000000000000 : ℝ) v650 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h649) (by norm_num) (by norm_num)
  let v651 : ℝ := -j192.tangent
  have h651 : Bounds (366188081411/50000000000000 : ℝ) v651 (146475232637/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_tangent) (by norm_num) (by norm_num)
  let v652 : ℝ := j6.tangent+v651
  have h652 : Bounds (366188081411/50000000000000 : ℝ) v652 (146475232637/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h651) (by norm_num) (by norm_num)
  obtain ⟨j193,hj193⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j192=z := ⟨_,rfl⟩
  have j193_value : Bounds (-46102485455869/100000000000000 : ℝ) j193.value (-23051242727897/50000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h650
  have j193_tangent : Bounds (366188081411/50000000000000 : ℝ) j193.tangent (146475232637/20000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h652
  let v653 : ℝ := j176.value*j193.value
  have h653 : Bounds (-3497578583167/100000000000000 : ℝ) v653 (-87439464577/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v654 : ℝ := j176.tangent*j193.value
  have h654 : Bounds (421876661211/100000000000000 : ℝ) v654 (527345827/125000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j176_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v655 : ℝ := j176.value*j193.tangent
  have h655 : Bounds (3472620777/6250000000000 : ℝ) v655 (55561932461/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v656 : ℝ := v654+v655
  have h656 : Bounds (477438593643/100000000000000 : ℝ) v656 (477438594061/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h654 h655) (by norm_num) (by norm_num)
  obtain ⟨j194,hj194⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j193=z := ⟨_,rfl⟩
  have j194_value : Bounds (-3497578583167/100000000000000 : ℝ) j194.value (-87439464577/2500000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h653
  have j194_tangent : Bounds (477438593643/100000000000000 : ℝ) j194.tangent (477438594061/100000000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h656
  let v657 : ℝ := j167.value*j165.value
  have h657 : Bounds (69353574212359/100000000000000 : ℝ) v657 (13870714842493/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v658 : ℝ := j167.tangent*j165.value
  have h658 : Bounds (-85381314450121/100000000000000 : ℝ) v658 (-85381314449739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v659 : ℝ := j167.value*j165.tangent
  have h659 : Bounds (84279575485669/100000000000000 : ℝ) v659 (42139787742921/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v660 : ℝ := v658+v659
  have h660 : Bounds (-275434741113/25000000000000 : ℝ) v660 (-1101738963897/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h658 h659) (by norm_num) (by norm_num)
  obtain ⟨j195,hj195⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j165=z := ⟨_,rfl⟩
  have j195_value : Bounds (69353574212359/100000000000000 : ℝ) j195.value (13870714842493/20000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h657
  have j195_tangent : Bounds (-275434741113/25000000000000 : ℝ) j195.tangent (-1101738963897/100000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h660
  let v661 : ℝ := -j195.value
  have h661 : Bounds (-13870714842493/20000000000000 : ℝ) v661 (-69353574212359/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_value) (by norm_num) (by norm_num)
  let v662 : ℝ := j0.value+v661
  have h662 : Bounds (6129285157507/20000000000000 : ℝ) v662 (30646425787641/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h661) (by norm_num) (by norm_num)
  let v663 : ℝ := -j195.tangent
  have h663 : Bounds (1101738963897/100000000000000 : ℝ) v663 (275434741113/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_tangent) (by norm_num) (by norm_num)
  let v664 : ℝ := j0.tangent+v663
  have h664 : Bounds (1101738963897/100000000000000 : ℝ) v664 (275434741113/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h663) (by norm_num) (by norm_num)
  obtain ⟨j196,hj196⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j195=z := ⟨_,rfl⟩
  have j196_value : Bounds (6129285157507/20000000000000 : ℝ) j196.value (30646425787641/100000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h662
  have j196_tangent : Bounds (1101738963897/100000000000000 : ℝ) j196.tangent (275434741113/25000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h664
  let v665 : ℝ := j182.value*j196.value
  have h665 : Bounds (361122779531/50000000000000 : ℝ) v665 (180561389783/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v666 : ℝ := j182.tangent*j196.value
  have h666 : Bounds (-87116997821/100000000000000 : ℝ) v666 (-3484679899/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j182_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v667 : ℝ := j182.value*j196.tangent
  have h667 : Bounds (25964726831/100000000000000 : ℝ) v667 (25964726847/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v668 : ℝ := v666+v667
  have h668 : Bounds (-6115227099/10000000000000 : ℝ) v668 (-15288067657/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h666 h667) (by norm_num) (by norm_num)
  obtain ⟨j197,hj197⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j196=z := ⟨_,rfl⟩
  have j197_value : Bounds (361122779531/50000000000000 : ℝ) j197.value (180561389783/25000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h665
  have j197_tangent : Bounds (-6115227099/10000000000000 : ℝ) j197.tangent (-15288067657/25000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h668
  let v669 : ℝ := j194.value+j197.value
  have h669 : Bounds (-555066604821/20000000000000 : ℝ) v669 (-693833255987/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_value j197_value) (by norm_num) (by norm_num)
  let v670 : ℝ := j194.tangent+j197.tangent
  have h670 : Bounds (416286322653/100000000000000 : ℝ) v670 (416286323433/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_tangent j197_tangent) (by norm_num) (by norm_num)
  obtain ⟨j198,hj198⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j194 j197=z := ⟨_,rfl⟩
  have j198_value : Bounds (-555066604821/20000000000000 : ℝ) j198.value (-693833255987/25000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h669
  have j198_tangent : Bounds (416286322653/100000000000000 : ℝ) j198.tangent (416286323433/100000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h670
  let v671 : ℝ := j158.value*j164.value
  have h671 : Bounds (126605167307/50000000000000 : ℝ) v671 (50642066923/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v672 : ℝ := j158.tangent*j164.value
  have h672 : Bounds (80207656491/25000000000000 : ℝ) v672 (64166125193/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v673 : ℝ := j158.value*j164.tangent
  have h673 : Bounds (307705258917/100000000000000 : ℝ) v673 (307705258919/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v674 : ℝ := v672+v673
  have h674 : Bounds (628535884881/100000000000000 : ℝ) v674 (157133971221/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h672 h673) (by norm_num) (by norm_num)
  obtain ⟨j199,hj199⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j164=z := ⟨_,rfl⟩
  have j199_value : Bounds (126605167307/50000000000000 : ℝ) j199.value (50642066923/20000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h671
  have j199_tangent : Bounds (628535884881/100000000000000 : ℝ) j199.tangent (157133971221/25000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h674
  let v675 : ℝ := j167.value*j199.value
  have h675 : Bounds (173458314001/6250000000000 : ℝ) v675 (2775333024031/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v676 : ℝ := j167.tangent*j199.value
  have h676 : Bounds (-854179414397/25000000000000 : ℝ) v676 (-85417941439/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v677 : ℝ := j167.value*j199.tangent
  have h677 : Bounds (3444560034939/50000000000000 : ℝ) v677 (3444560034959/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v678 : ℝ := v676+v677
  have h678 : Bounds (347240241229/10000000000000 : ℝ) v678 (1736201206179/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h676 h677) (by norm_num) (by norm_num)
  obtain ⟨j200,hj200⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j199=z := ⟨_,rfl⟩
  have j200_value : Bounds (173458314001/6250000000000 : ℝ) j200.value (2775333024031/100000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h675
  have j200_tangent : Bounds (347240241229/10000000000000 : ℝ) j200.tangent (1736201206179/50000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h678
  let v679 : ℝ := j198.value+j200.value
  have h679 : Bounds (-89/100000000000000 : ℝ) v679 (83/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_value j200_value) (by norm_num) (by norm_num)
  let v680 : ℝ := j198.tangent+j200.tangent
  have h680 : Bounds (3888688734943/100000000000000 : ℝ) v680 (3888688735791/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_tangent j200_tangent) (by norm_num) (by norm_num)
  obtain ⟨j201,hj201⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j198 j200=z := ⟨_,rfl⟩
  have j201_value : Bounds (-89/100000000000000 : ℝ) j201.value (83/100000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h679
  have j201_tangent : Bounds (3888688734943/100000000000000 : ℝ) j201.tangent (3888688735791/100000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h680
  let v681 : ℝ := j164.value*j151.value
  have h681 : Bounds (65721987617/1562500000000 : ℝ) v681 (4206207207491/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v682 : ℝ := j164.tangent*j151.value
  have h682 : Bounds (5111450446179/100000000000000 : ℝ) v682 (638931305773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v683 : ℝ := j164.value*j151.tangent
  have h683 : Bounds (0 : ℝ) v683 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v684 : ℝ := v682+v683
  have h684 : Bounds (5111450446179/100000000000000 : ℝ) v684 (638931305773/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h682 h683) (by norm_num) (by norm_num)
  obtain ⟨j202,hj202⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j151=z := ⟨_,rfl⟩
  have j202_value : Bounds (65721987617/1562500000000 : ℝ) j202.value (4206207207491/100000000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h681
  have j202_tangent : Bounds (5111450446179/100000000000000 : ℝ) j202.tangent (638931305773/12500000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h684
  let v685 : ℝ := j167.value*j202.value
  have h685 : Bounds (23051242727897/50000000000000 : ℝ) v685 (46102485455869/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v686 : ℝ := j167.tangent*j202.value
  have h686 : Bounds (-28378427877277/50000000000000 : ℝ) v686 (-7094606969287/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v687 : ℝ := j167.value*j202.tangent
  have h687 : Bounds (56024479591369/100000000000000 : ℝ) v687 (28012239795737/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v688 : ℝ := v686+v687
  have h688 : Bounds (-146475232637/20000000000000 : ℝ) v688 (-366188081411/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h686 h687) (by norm_num) (by norm_num)
  obtain ⟨j203,hj203⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j202=z := ⟨_,rfl⟩
  have j203_value : Bounds (23051242727897/50000000000000 : ℝ) j203.value (46102485455869/100000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h685
  have j203_tangent : Bounds (-146475232637/20000000000000 : ℝ) j203.tangent (-366188081411/50000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h688
  let v689 : ℝ := -j203.value
  have h689 : Bounds (-46102485455869/100000000000000 : ℝ) v689 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_value) (by norm_num) (by norm_num)
  let v690 : ℝ := j6.value+v689
  have h690 : Bounds (-46102485455869/100000000000000 : ℝ) v690 (-23051242727897/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h689) (by norm_num) (by norm_num)
  let v691 : ℝ := -j203.tangent
  have h691 : Bounds (366188081411/50000000000000 : ℝ) v691 (146475232637/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_tangent) (by norm_num) (by norm_num)
  let v692 : ℝ := j6.tangent+v691
  have h692 : Bounds (366188081411/50000000000000 : ℝ) v692 (146475232637/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h691) (by norm_num) (by norm_num)
  obtain ⟨j204,hj204⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j203=z := ⟨_,rfl⟩
  have j204_value : Bounds (-46102485455869/100000000000000 : ℝ) j204.value (-23051242727897/50000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h690
  have j204_tangent : Bounds (366188081411/50000000000000 : ℝ) j204.tangent (146475232637/20000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h692
  let v693 : ℝ := j204.value*j115.value
  have h693 : Bounds (-31084057194233/100000000000000 : ℝ) v693 (-6216811438833/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v694 : ℝ := j204.tangent*j115.value
  have h694 : Bounds (246897995929/50000000000000 : ℝ) v694 (61724499013/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v695 : ℝ := j204.value*j115.tangent
  have h695 : Bounds (-1294713572119/4000000000000 : ℝ) v695 (-16183919651441/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v696 : ℝ := v694+v695
  have h696 : Bounds (-31874043311117/100000000000000 : ℝ) v696 (-15937021655389/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h694 h695) (by norm_num) (by norm_num)
  obtain ⟨j205,hj205⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j115=z := ⟨_,rfl⟩
  have j205_value : Bounds (-31084057194233/100000000000000 : ℝ) j205.value (-6216811438833/20000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h693
  have j205_tangent : Bounds (-31874043311117/100000000000000 : ℝ) j205.tangent (-15937021655389/50000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h696
  let v697 : ℝ := j164.value*j160.value
  have h697 : Bounds (1581885991791/25000000000000 : ℝ) v697 (98867874487/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v698 : ℝ := j164.tangent*j160.value
  have h698 : Bounds (768933289273/10000000000000 : ℝ) v698 (7689332892739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v699 : ℝ := j164.value*j160.tangent
  have h699 : Bounds (0 : ℝ) v699 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v700 : ℝ := v698+v699
  have h700 : Bounds (768933289273/10000000000000 : ℝ) v700 (7689332892739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h698 h699) (by norm_num) (by norm_num)
  obtain ⟨j206,hj206⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j160=z := ⟨_,rfl⟩
  have j206_value : Bounds (1581885991791/25000000000000 : ℝ) j206.value (98867874487/1562500000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h697
  have j206_tangent : Bounds (768933289273/10000000000000 : ℝ) j206.tangent (7689332892739/100000000000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h700
  let v701 : ℝ := j167.value*j206.value
  have h701 : Bounds (69353574212359/100000000000000 : ℝ) v701 (13870714842493/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v702 : ℝ := j167.tangent*j206.value
  have h702 : Bounds (-85381314450121/100000000000000 : ℝ) v702 (-85381314449739/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v703 : ℝ := j167.value*j206.tangent
  have h703 : Bounds (84279575485669/100000000000000 : ℝ) v703 (42139787742921/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v704 : ℝ := v702+v703
  have h704 : Bounds (-275434741113/25000000000000 : ℝ) v704 (-1101738963897/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h702 h703) (by norm_num) (by norm_num)
  obtain ⟨j207,hj207⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j206=z := ⟨_,rfl⟩
  have j207_value : Bounds (69353574212359/100000000000000 : ℝ) j207.value (13870714842493/20000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h701
  have j207_tangent : Bounds (-275434741113/25000000000000 : ℝ) j207.tangent (-1101738963897/100000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h704
  let v705 : ℝ := -j207.value
  have h705 : Bounds (-13870714842493/20000000000000 : ℝ) v705 (-69353574212359/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_value) (by norm_num) (by norm_num)
  let v706 : ℝ := j0.value+v705
  have h706 : Bounds (6129285157507/20000000000000 : ℝ) v706 (30646425787641/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h705) (by norm_num) (by norm_num)
  let v707 : ℝ := -j207.tangent
  have h707 : Bounds (1101738963897/100000000000000 : ℝ) v707 (275434741113/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_tangent) (by norm_num) (by norm_num)
  let v708 : ℝ := j0.tangent+v707
  have h708 : Bounds (1101738963897/100000000000000 : ℝ) v708 (275434741113/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h707) (by norm_num) (by norm_num)
  obtain ⟨j208,hj208⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j207=z := ⟨_,rfl⟩
  have j208_value : Bounds (6129285157507/20000000000000 : ℝ) j208.value (30646425787641/100000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h706
  have j208_tangent : Bounds (1101738963897/100000000000000 : ℝ) j208.tangent (275434741113/25000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h708
  let v709 : ℝ := j208.value*j144.value
  have h709 : Bounds (651023624101/2500000000000 : ℝ) v709 (13020472482071/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v710 : ℝ := j208.tangent*j144.value
  have h710 : Bounds (936171934779/100000000000000 : ℝ) v710 (234042983813/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v711 : ℝ := j208.value*j144.tangent
  have h711 : Bounds (126184678983/400000000000 : ℝ) v711 (6309233949177/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v712 : ℝ := v710+v711
  have h712 : Bounds (32482341680529/100000000000000 : ℝ) v712 (32482341681137/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h710 h711) (by norm_num) (by norm_num)
  obtain ⟨j209,hj209⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j144=z := ⟨_,rfl⟩
  have j209_value : Bounds (651023624101/2500000000000 : ℝ) j209.value (13020472482071/50000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h709
  have j209_tangent : Bounds (32482341680529/100000000000000 : ℝ) j209.tangent (32482341681137/100000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h712
  let v713 : ℝ := j205.value+j209.value
  have h713 : Bounds (-5043112230193/100000000000000 : ℝ) v713 (-5043112230023/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_value j209_value) (by norm_num) (by norm_num)
  let v714 : ℝ := j205.tangent+j209.tangent
  have h714 : Bounds (152074592353/25000000000000 : ℝ) v714 (608298370359/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_tangent j209_tangent) (by norm_num) (by norm_num)
  obtain ⟨j210,hj210⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j205 j209=z := ⟨_,rfl⟩
  have j210_value : Bounds (-5043112230193/100000000000000 : ℝ) j210.value (-5043112230023/100000000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h713
  have j210_tangent : Bounds (152074592353/25000000000000 : ℝ) j210.tangent (608298370359/100000000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h714
  let v715 : ℝ := j210.value*j178.value
  have h715 : Bounds (-218598661449/6250000000000 : ℝ) v715 (-1748789291531/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v716 : ℝ := j210.tangent*j178.value
  have h716 : Bounds (210938330531/50000000000000 : ℝ) v716 (421876661721/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j210_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v717 : ℝ := j210.value*j178.tangent
  have h717 : Bounds (27780966219/50000000000000 : ℝ) v717 (6945241557/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v718 : ℝ := v716+v717
  have h718 : Bounds (954877187/200000000000 : ℝ) v718 (477438594177/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h716 h717) (by norm_num) (by norm_num)
  obtain ⟨j211,hj211⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j178=z := ⟨_,rfl⟩
  have j211_value : Bounds (-218598661449/6250000000000 : ℝ) j211.value (-1748789291531/50000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h715
  have j211_tangent : Bounds (954877187/200000000000 : ℝ) j211.tangent (477438594177/100000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h718
  let v719 : ℝ := j204.value*j126.value
  have h719 : Bounds (-39174300284981/100000000000000 : ℝ) v719 (-391743002849/1000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v720 : ℝ := j204.tangent*j126.value
  have h720 : Bounds (622316203567/100000000000000 : ℝ) v720 (622316203877/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v721 : ℝ := j204.value*j126.tangent
  have h721 : Bounds (-47456001622367/100000000000000 : ℝ) v721 (-47456001622251/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v722 : ℝ := v720+v721
  have h722 : Bounds (-117084213547/250000000000 : ℝ) v722 (-23416842709187/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h720 h721) (by norm_num) (by norm_num)
  obtain ⟨j212,hj212⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j126=z := ⟨_,rfl⟩
  have j212_value : Bounds (-39174300284981/100000000000000 : ℝ) j212.value (-391743002849/1000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h719
  have j212_tangent : Bounds (-117084213547/250000000000 : ℝ) j212.tangent (-23416842709187/50000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h722
  let v723 : ℝ := j208.value*j150.value
  have h723 : Bounds (7521538312189/20000000000000 : ℝ) v723 (9401922890271/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v724 : ℝ := j208.tangent*j150.value
  have h724 : Bounds (675998229323/50000000000000 : ℝ) v724 (21124944677/1562500000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v725 : ℝ := j208.value*j150.tangent
  have h725 : Bounds (45670652736133/100000000000000 : ℝ) v725 (5708831592039/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v726 : ℝ := v724+v725
  have h726 : Bounds (47022649194779/100000000000000 : ℝ) v726 (1175566229891/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h724 h725) (by norm_num) (by norm_num)
  obtain ⟨j213,hj213⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j150=z := ⟨_,rfl⟩
  have j213_value : Bounds (7521538312189/20000000000000 : ℝ) j213.value (9401922890271/25000000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h723
  have j213_tangent : Bounds (47022649194779/100000000000000 : ℝ) j213.tangent (1175566229891/2500000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h726
  let v727 : ℝ := j212.value+j213.value
  have h727 : Bounds (-391652181009/25000000000000 : ℝ) v727 (-195826090477/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_value j213_value) (by norm_num) (by norm_num)
  let v728 : ℝ := j212.tangent+j213.tangent
  have h728 : Bounds (188963775979/100000000000000 : ℝ) v728 (94481888633/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_tangent j213_tangent) (by norm_num) (by norm_num)
  obtain ⟨j214,hj214⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j212 j213=z := ⟨_,rfl⟩
  have j214_value : Bounds (-391652181009/25000000000000 : ℝ) j214.value (-195826090477/12500000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h727
  have j214_tangent : Bounds (188963775979/100000000000000 : ℝ) j214.tangent (94481888633/50000000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h728
  let v729 : ℝ := j214.value*j185.value
  have h729 : Bounds (361122779523/50000000000000 : ℝ) v729 (14444911183/2000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v730 : ℝ := j214.tangent*j185.value
  have h730 : Bounds (-87116997931/100000000000000 : ℝ) v730 (-87116997337/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j214_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v731 : ℝ := j214.value*j185.tangent
  have h731 : Bounds (25964726833/100000000000000 : ℝ) v731 (5192945369/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v732 : ℝ := v730+v731
  have h732 : Bounds (-30576135549/50000000000000 : ℝ) v732 (-15288067623/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h730 h731) (by norm_num) (by norm_num)
  obtain ⟨j215,hj215⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j185=z := ⟨_,rfl⟩
  have j215_value : Bounds (361122779523/50000000000000 : ℝ) j215.value (14444911183/2000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h729
  have j215_tangent : Bounds (-30576135549/50000000000000 : ℝ) j215.tangent (-15288067623/25000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h732
  let v733 : ℝ := j211.value+j215.value
  have h733 : Bounds (-1387666512069/50000000000000 : ℝ) v733 (-346916627989/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_value j215_value) (by norm_num) (by norm_num)
  let v734 : ℝ := j211.tangent+j215.tangent
  have h734 : Bounds (208143161201/50000000000000 : ℝ) v734 (83257264737/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_tangent j215_tangent) (by norm_num) (by norm_num)
  obtain ⟨j216,hj216⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j211 j215=z := ⟨_,rfl⟩
  have j216_value : Bounds (-1387666512069/50000000000000 : ℝ) j216.value (-346916627989/12500000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h733
  have j216_tangent : Bounds (208143161201/50000000000000 : ℝ) j216.tangent (83257264737/20000000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h734
  let v735 : ℝ := j164.value*j158.value
  have h735 : Bounds (126605167307/50000000000000 : ℝ) v735 (50642066923/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v736 : ℝ := j164.tangent*j158.value
  have h736 : Bounds (307705258917/100000000000000 : ℝ) v736 (307705258919/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v737 : ℝ := j164.value*j158.tangent
  have h737 : Bounds (80207656491/25000000000000 : ℝ) v737 (64166125193/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v738 : ℝ := v736+v737
  have h738 : Bounds (628535884881/100000000000000 : ℝ) v738 (157133971221/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h736 h737) (by norm_num) (by norm_num)
  obtain ⟨j217,hj217⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j158=z := ⟨_,rfl⟩
  have j217_value : Bounds (126605167307/50000000000000 : ℝ) j217.value (50642066923/20000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h735
  have j217_tangent : Bounds (628535884881/100000000000000 : ℝ) j217.tangent (157133971221/25000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h738
  let v739 : ℝ := j167.value*j217.value
  have h739 : Bounds (173458314001/6250000000000 : ℝ) v739 (2775333024031/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v740 : ℝ := j167.tangent*j217.value
  have h740 : Bounds (-854179414397/25000000000000 : ℝ) v740 (-85417941439/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v741 : ℝ := j167.value*j217.tangent
  have h741 : Bounds (3444560034939/50000000000000 : ℝ) v741 (3444560034959/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v742 : ℝ := v740+v741
  have h742 : Bounds (347240241229/10000000000000 : ℝ) v742 (1736201206179/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h740 h741) (by norm_num) (by norm_num)
  obtain ⟨j218,hj218⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j217=z := ⟨_,rfl⟩
  have j218_value : Bounds (173458314001/6250000000000 : ℝ) j218.value (2775333024031/100000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h739
  have j218_tangent : Bounds (347240241229/10000000000000 : ℝ) j218.tangent (1736201206179/50000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h742
  let v743 : ℝ := j216.value+j218.value
  have h743 : Bounds (-61/50000000000000 : ℝ) v743 (119/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_value j218_value) (by norm_num) (by norm_num)
  let v744 : ℝ := j216.tangent+j218.tangent
  have h744 : Bounds (972172183673/25000000000000 : ℝ) v744 (3888688736043/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_tangent j218_tangent) (by norm_num) (by norm_num)
  obtain ⟨j219,hj219⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j216 j218=z := ⟨_,rfl⟩
  have j219_value : Bounds (-61/50000000000000 : ℝ) j219.value (119/100000000000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h743
  have j219_tangent : Bounds (972172183673/25000000000000 : ℝ) j219.tangent (3888688736043/100000000000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h744
  let v745 : ℝ := j210.value*j193.value
  have h745 : Bounds (465000016473/20000000000000 : ℝ) v745 (145312505153/6250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v746 : ℝ := j210.tangent*j193.value
  have h746 : Bounds (-70110166931/25000000000000 : ℝ) v746 (-56088133457/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j210_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v747 : ℝ := j210.value*j193.tangent
  have h747 : Bounds (-36934551857/100000000000000 : ℝ) v747 (-36934551837/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v748 : ℝ := v746+v747
  have h748 : Bounds (-317375219581/100000000000000 : ℝ) v748 (-158687609561/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h746 h747) (by norm_num) (by norm_num)
  obtain ⟨j220,hj220⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j193=z := ⟨_,rfl⟩
  have j220_value : Bounds (465000016473/20000000000000 : ℝ) j220.value (145312505153/6250000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h745
  have j220_tangent : Bounds (-317375219581/100000000000000 : ℝ) j220.tangent (-158687609561/50000000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h748
  let v749 : ℝ := j214.value*j196.value
  have h749 : Bounds (-96021915999/20000000000000 : ℝ) v749 (-19204383197/4000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v750 : ℝ := j214.tangent*j196.value
  have h750 : Bounds (5791064337/10000000000000 : ℝ) v750 (28955321883/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j214_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v751 : ℝ := j214.value*j196.tangent
  have h751 : Bounds (-8629969367/50000000000000 : ℝ) v751 (-8629969361/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v752 : ℝ := v750+v751
  have h752 : Bounds (10162676159/25000000000000 : ℝ) v752 (10162676261/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h750 h751) (by norm_num) (by norm_num)
  obtain ⟨j221,hj221⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j196=z := ⟨_,rfl⟩
  have j221_value : Bounds (-96021915999/20000000000000 : ℝ) j221.value (-19204383197/4000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h749
  have j221_tangent : Bounds (10162676159/25000000000000 : ℝ) j221.tangent (10162676261/25000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h752
  let v753 : ℝ := j220.value+j221.value
  have h753 : Bounds (184489050237/10000000000000 : ℝ) v753 (1844890502523/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_value j221_value) (by norm_num) (by norm_num)
  let v754 : ℝ := j220.tangent+j221.tangent
  have h754 : Bounds (-55344902989/20000000000000 : ℝ) v754 (-138362257039/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_tangent j221_tangent) (by norm_num) (by norm_num)
  obtain ⟨j222,hj222⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j220 j221=z := ⟨_,rfl⟩
  have j222_value : Bounds (184489050237/10000000000000 : ℝ) j222.value (1844890502523/100000000000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h753
  have j222_tangent : Bounds (-55344902989/20000000000000 : ℝ) j222.tangent (-138362257039/50000000000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h754
  let v755 : ℝ := j164.value*j164.value
  have h755 : Bounds (380913123433/100000000000000 : ℝ) v755 (76182624687/20000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v756 : ℝ := j164.tangent*j164.value
  have h756 : Bounds (231445867819/50000000000000 : ℝ) v756 (11572293391/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v757 : ℝ := j164.value*j164.tangent
  have h757 : Bounds (231445867819/50000000000000 : ℝ) v757 (11572293391/2500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v758 : ℝ := v756+v757
  have h758 : Bounds (231445867819/25000000000000 : ℝ) v758 (11572293391/1250000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h756 h757) (by norm_num) (by norm_num)
  obtain ⟨j223,hj223⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j164=z := ⟨_,rfl⟩
  have j223_value : Bounds (380913123433/100000000000000 : ℝ) j223.value (76182624687/20000000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h755
  have j223_tangent : Bounds (231445867819/25000000000000 : ℝ) j223.tangent (11572293391/1250000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h758
  let v759 : ℝ := j167.value*j223.value
  have h759 : Bounds (835006021659/20000000000000 : ℝ) v759 (4175030108321/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v760 : ℝ := j167.tangent*j223.value
  have h760 : Bounds (-5139887346329/100000000000000 : ℝ) v760 (-5139887346281/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v761 : ℝ := j167.value*j223.tangent
  have h761 : Bounds (5073563535307/50000000000000 : ℝ) v761 (2536781767667/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v762 : ℝ := v760+v761
  have h762 : Bounds (1001447944857/20000000000000 : ℝ) v762 (5007239724387/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h760 h761) (by norm_num) (by norm_num)
  obtain ⟨j224,hj224⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j223=z := ⟨_,rfl⟩
  have j224_value : Bounds (835006021659/20000000000000 : ℝ) j224.value (4175030108321/100000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h759
  have j224_tangent : Bounds (1001447944857/20000000000000 : ℝ) j224.tangent (5007239724387/100000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h762
  let v763 : ℝ := j222.value+j224.value
  have h763 : Bounds (1203984122133/20000000000000 : ℝ) v763 (1504980152711/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_value j224_value) (by norm_num) (by norm_num)
  let v764 : ℝ := j222.tangent+j224.tangent
  have h764 : Bounds (236525760467/5000000000000 : ℝ) v764 (4730515210309/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_tangent j224_tangent) (by norm_num) (by norm_num)
  obtain ⟨j225,hj225⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j222 j224=z := ⟨_,rfl⟩
  have j225_value : Bounds (1203984122133/20000000000000 : ℝ) j225.value (1504980152711/25000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h763
  have j225_tangent : Bounds (236525760467/5000000000000 : ℝ) j225.tangent (4730515210309/100000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h764
  have hm13 : jetIter c d 1 3=!![j190,j201;j219,j225] := by
    rw [jetIter,hm12]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj80,← hj85,← hj151,← hj152,← hj153,← hj154,← hj155,← hj156,← hj157,← hj158,← hj159,← hj160,← hj161,← hj162,← hj163,← hj164,← hj165,← hj166,← hj167,← hj168,← hj169,← hj170,← hj171,← hj172,← hj173,← hj174,← hj175,← hj176,← hj177,← hj178,← hj179,← hj180,← hj181,← hj182,← hj183,← hj184,← hj185,← hj186,← hj187,← hj188,← hj189,← hj190,← hj191,← hj192,← hj193,← hj194,← hj195,← hj196,← hj197,← hj198,← hj199,← hj200,← hj201,← hj202,← hj203,← hj204,← hj205,← hj206,← hj207,← hj208,← hj209,← hj210,← hj211,← hj212,← hj213,← hj214,← hj215,← hj216,← hj217,← hj218,← hj219,← hj220,← hj221,← hj222,← hj223,← hj224,← hj225]
    all_goals rfl
  let v765 : ℝ := j190.value⁻¹
  have h765 : Bounds (1661151474644033/100000000000000 : ℝ) v765 (415287868677841/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j190_value (by norm_num)) (by norm_num) (by norm_num)
  let v766 : ℝ := -j190.tangent
  have h766 : Bounds (-888830873339/50000000000000 : ℝ) v766 (-888830872731/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j190_tangent) (by norm_num) (by norm_num)
  let v767 : ℝ := j190.value*j190.value
  have h767 : Bounds (362394441583/100000000000000 : ℝ) v767 (362394441613/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j190_value j190_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v768 : ℝ := v767⁻¹
  have h768 : Bounds (27594242217100481/100000000000000 : ℝ) v768 (3449280277423101/12500000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h767 (by norm_num)) (by norm_num) (by norm_num)
  let v769 : ℝ := v766*v768
  have h769 : Bounds (-19621291528787/4000000000000 : ℝ) v769 (-1532913399511/312500000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn h766 h768 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j226,hj226⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j190=z := ⟨_,rfl⟩
  have j226_value : Bounds (1661151474644033/100000000000000 : ℝ) j226.value (415287868677841/25000000000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h765
  have j226_tangent : Bounds (-19621291528787/4000000000000 : ℝ) j226.tangent (-1532913399511/312500000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h769
  let v770 : ℝ := j201.value*j226.value
  have h770 : Bounds (-1479/100000000000000 : ℝ) v770 (1379/100000000000000 : ℝ) := by
    exact mul_corners j201_value j226_value (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v771 : ℝ := j201.tangent*j226.value
  have h771 : Bounds (32298505132411/50000000000000 : ℝ) v771 (64597010281527/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j201_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v772 : ℝ := j201.value*j226.tangent
  have h772 : Bounds (-51/12500000000000 : ℝ) v772 (437/100000000000000 : ℝ) := by
    exact mul_corners j201_value j226_tangent (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v773 : ℝ := v771+v772
  have h773 : Bounds (32298505132207/50000000000000 : ℝ) v773 (16149252570491/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h771 h772) (by norm_num) (by norm_num)
  obtain ⟨j227,hj227⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j201 j226=z := ⟨_,rfl⟩
  have j227_value : Bounds (-1479/100000000000000 : ℝ) j227.value (1379/100000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h770
  have j227_tangent : Bounds (32298505132207/50000000000000 : ℝ) j227.tangent (16149252570491/25000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h773
  have he01 : jacobian c d 0 1=j227.tangent := by
    simp only [jacobian,shapeJet,hm13,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj227,← hj226]
    rfl
  let v774 : ℝ := j225.value*j226.value
  have h774 : Bounds (99999999996461/100000000000000 : ℝ) v774 (100000000003489/100000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_value j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v775 : ℝ := j225.tangent*j226.value
  have h775 : Bounds (78581023158211/100000000000000 : ℝ) v775 (39290511588747/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v776 : ℝ := j225.value*j226.tangent
  have h776 : Bounds (-29529654321381/100000000000000 : ℝ) v776 (-14764827148929/50000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j225_value j226_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v777 : ℝ := v775+v776
  have h777 : Bounds (4905136883683/10000000000000 : ℝ) v777 (12262842219909/25000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h775 h776) (by norm_num) (by norm_num)
  obtain ⟨j228,hj228⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j225 j226=z := ⟨_,rfl⟩
  have j228_value : Bounds (99999999996461/100000000000000 : ℝ) j228.value (100000000003489/100000000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h774
  have j228_tangent : Bounds (4905136883683/10000000000000 : ℝ) j228.tangent (12262842219909/25000000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h777
  have he11 : jacobian c d 1 1=j228.tangent := by
    simp only [jacobian,shapeJet,hm13,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj228,← hj226]
    rfl
  rw [he01,he11]
  exact ⟨enlarge j227_tangent (by norm_num) (by norm_num),
    enlarge j228_tangent (by norm_num) (by norm_num)⟩

theorem jacobian_bounds {c d : ℝ}
    (hc : Bounds (318481427627118/10^15) c (318481427627119/10^15))
    (hd : Bounds (-1025232119675749/10^15) d (-1025232119675748/10^15)) :
    Bounds (11123986249/10^10) (jacobian c d 0 0) (11123986253/10^10) ∧
    Bounds (6459701025/10^10) (jacobian c d 0 1) (6459701029/10^10) ∧
    Bounds (7515015701/10^10) (jacobian c d 1 0) (7515015708/10^10) ∧
    Bounds (4905136882/10^10) (jacobian c d 1 1) (4905136890/10^10) := by
  constructor
  · convert (column_0_bounds hc hd).1 using 1 <;> norm_num
  constructor
  · convert (column_1_bounds hc hd).1 using 1 <;> norm_num
  constructor
  · convert (column_0_bounds hc hd).2 using 1 <;> norm_num
  · convert (column_1_bounds hc hd).2 using 1 <;> norm_num
end BfgsVerification.LShapeIntervalCertificate

