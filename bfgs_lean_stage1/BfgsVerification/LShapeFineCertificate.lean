import BfgsVerification.LShapeDerivative
import BfgsVerification.LShapeIntervalTools
noncomputable section
open Matrix
namespace BfgsVerification.LShapeFineCertificate
open IntervalBounds LShapeIntervalTools LShapeDerivative
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000


theorem column_0_bounds {c d : ℝ}
    (hc : Bounds (318481427627118630646451312501/1000000000000000000000000000000 : ℝ) c (39810178453389828830806414063/125000000000000000000000000000 : ℝ))
    (hd : Bounds (-205046423935149745096270174003/200000000000000000000000000000 : ℝ) d (-256308029918937181370337717503/250000000000000000000000000000 : ℝ)) :
    Bounds (222479725014657906929/200000000000000000000 : ℝ) (jacobian c d 0 0) (222479725014657906931/200000000000000000000 : ℝ) ∧
    Bounds (30060062817099939949/40000000000000000000 : ℝ) (jacobian c d 1 0) (150300314085499699747/200000000000000000000 : ℝ) := by

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
  have h256 : Bounds (1318481427627118630646451312501/1000000000000000000000000000000 : ℝ) v256 (164810178453389828830806414063/125000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hc h255) (by norm_num) (by norm_num)
  obtain ⟨j77,hj77⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (c+(-(-1 : ℝ)))=z := ⟨_,rfl⟩
  have j77_value : Bounds (1318481427627118630646451312501/1000000000000000000000000000000 : ℝ) j77.value (164810178453389828830806414063/125000000000000000000000000000 : ℝ) := by
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
  have h271 : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) v271 (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v272 : ℝ := j77.tangent*j83.value
  have h272 : Bounds (0 : ℝ) v272 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v273 : ℝ := j77.value*j83.tangent
  have h273 : Bounds (20923167186465505613285970535294189453/2000000000000000000000000000000000000000 : ℝ) v273 (2142532319894067774800483382819/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v274 : ℝ := v272+v273
  have h274 : Bounds (20923167186465505613285970535294189453/2000000000000000000000000000000000000000 : ℝ) v274 (2142532319894067774800483382819/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h272 h273) (by norm_num) (by norm_num)
  obtain ⟨j84,hj84⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j83=z := ⟨_,rfl⟩
  have j84_value : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) j84.value (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h271
  have j84_tangent : Bounds (20923167186465505613285970535294189453/2000000000000000000000000000000000000000 : ℝ) j84.tangent (2142532319894067774800483382819/204800000000000000000000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h274
  let v275 : ℝ := -(-1/8 : ℝ)
  have h275 : Bounds (1/8 : ℝ) v275 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (-1/8 : ℝ))) (by norm_num) (by norm_num)
  let v276 : ℝ := d+v275
  have h276 : Bounds (-180046423935149745096270174003/200000000000000000000000000000 : ℝ) v276 (-225058029918937181370337717503/250000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hd h275) (by norm_num) (by norm_num)
  obtain ⟨j85,hj85⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (d+(-(-1/8 : ℝ)))=z := ⟨_,rfl⟩
  have j85_value : Bounds (-180046423935149745096270174003/200000000000000000000000000000 : ℝ) j85.value (-225058029918937181370337717503/250000000000000000000000000000 : ℝ) := by
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
  have h291 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v291 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v292 : ℝ := j85.tangent*j89.value
  have h292 : Bounds (0 : ℝ) v292 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v293 : ℝ := j85.value*j89.tangent
  have h293 : Bounds (-11342924707914433941065020962189/102400000000000000000000000000000 : ℝ) v293 (-14178655884893042426331276202689/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v294 : ℝ := v292+v293
  have h294 : Bounds (-11342924707914433941065020962189/102400000000000000000000000000000 : ℝ) v294 (-14178655884893042426331276202689/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h292 h293) (by norm_num) (by norm_num)
  obtain ⟨j90,hj90⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j89=z := ⟨_,rfl⟩
  have j90_value : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) j90.value (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h291
  have j90_tangent : Bounds (-11342924707914433941065020962189/102400000000000000000000000000000 : ℝ) j90.tangent (-14178655884893042426331276202689/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h294
  let v295 : ℝ := j84.value+j90.value
  have h295 : Bounds (153043427393832086484397702767387/1024000000000000000000000000000000 : ℝ) v295 (19130428424229010810549712845977/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_value j90_value) (by norm_num) (by norm_num)
  let v296 : ℝ := j84.tangent+j90.tangent
  have h296 : Bounds (-200618331014988282298140220132459716797/2000000000000000000000000000000000000000 : ℝ) v296 (-102716585479674000536647792707417/1024000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_tangent j90_tangent) (by norm_num) (by norm_num)
  obtain ⟨j91,hj91⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j84 j90=z := ⟨_,rfl⟩
  have j91_value : Bounds (153043427393832086484397702767387/1024000000000000000000000000000000 : ℝ) j91.value (19130428424229010810549712845977/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h295
  have j91_tangent : Bounds (-200618331014988282298140220132459716797/2000000000000000000000000000000000000000 : ℝ) j91.tangent (-102716585479674000536647792707417/1024000000000000000000000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h296
  let v297 : ℝ := j91.value⁻¹
  have h297 : Bounds (8363639143457827467032759059691183977931/1250000000000000000000000000000000000000 : ℝ) v297 (33454556573831309868131036238858513246789/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j91_value (by norm_num)) (by norm_num) (by norm_num)
  let v298 : ℝ := -j91.tangent
  have h298 : Bounds (102716585479674000536647792707417/1024000000000000000000000000000000 : ℝ) v298 (200618331014988282298140220132459716797/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j91_tangent) (by norm_num) (by norm_num)
  let v299 : ℝ := j91.value*j91.value
  have h299 : Bounds (111686185209518210942120195720437490149/5000000000000000000000000000000000000000 : ℝ) v299 (223372370419036421884240391442127262067/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j91_value j91_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v300 : ℝ := v299⁻¹
  have h300 : Bounds (89536588444134376828468553548047042179873/2000000000000000000000000000000000000000 : ℝ) v300 (22384147111033594207117138387137251711531/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h299 (by norm_num)) (by norm_num) (by norm_num)
  let v301 : ℝ := v298*v300
  have h301 : Bounds (44906702346095312706663799932914960988043/10000000000000000000000000000000000000000 : ℝ) v301 (44906702346095312706663799933342633748443/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn h298 h300 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j92,hj92⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j91=z := ⟨_,rfl⟩
  have j92_value : Bounds (8363639143457827467032759059691183977931/1250000000000000000000000000000000000000 : ℝ) j92.value (33454556573831309868131036238858513246789/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h297
  have j92_tangent : Bounds (44906702346095312706663799932914960988043/10000000000000000000000000000000000000000 : ℝ) j92.tangent (44906702346095312706663799933342633748443/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h301
  let v302 : ℝ := j83.value*j77.value
  have h302 : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) v302 (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v303 : ℝ := j83.tangent*j77.value
  have h303 : Bounds (20923167186465505613285970535294189453/2000000000000000000000000000000000000000 : ℝ) v303 (2142532319894067774800483382819/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v304 : ℝ := j83.value*j77.tangent
  have h304 : Bounds (0 : ℝ) v304 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v305 : ℝ := v303+v304
  have h305 : Bounds (20923167186465505613285970535294189453/2000000000000000000000000000000000000000 : ℝ) v305 (2142532319894067774800483382819/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h303 h304) (by norm_num) (by norm_num)
  obtain ⟨j93,hj93⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j77=z := ⟨_,rfl⟩
  have j93_value : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) j93.value (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h302
  have j93_tangent : Bounds (20923167186465505613285970535294189453/2000000000000000000000000000000000000000 : ℝ) j93.tangent (2142532319894067774800483382819/204800000000000000000000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h305
  let v306 : ℝ := j92.value*j93.value
  have h306 : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) v306 (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v307 : ℝ := j92.tangent*j93.value
  have h307 : Bounds (7343260677199062337029587973690251079207/10000000000000000000000000000000000000000 : ℝ) v307 (7343260677199062337029587973776893691257/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v308 : ℝ := j92.value*j93.tangent
  have h308 : Bounds (174993820085835283201847206422326188793/2500000000000000000000000000000000000000 : ℝ) v308 (27999011213733645312295553027714382369/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j93_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v309 : ℝ := v307+v308
  have h309 : Bounds (8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) v309 (4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h307 h308) (by norm_num) (by norm_num)
  obtain ⟨j94,hj94⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j93=z := ⟨_,rfl⟩
  have j94_value : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) j94.value (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h306
  have j94_tangent : Bounds (8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) j94.tangent (4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h309
  let v310 : ℝ := -j94.value
  have h310 : Bounds (-21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v310 (-10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_value) (by norm_num) (by norm_num)
  let v311 : ℝ := j0.value+v310
  have h311 : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v311 (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h310) (by norm_num) (by norm_num)
  let v312 : ℝ := -j94.tangent
  have h312 : Bounds (-4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) v312 (-8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_tangent) (by norm_num) (by norm_num)
  let v313 : ℝ := j0.tangent+v312
  have h313 : Bounds (-4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) v313 (-8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h312) (by norm_num) (by norm_num)
  obtain ⟨j95,hj95⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j94=z := ⟨_,rfl⟩
  have j95_value : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) j95.value (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h311
  have j95_tangent : Bounds (-4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) j95.tangent (-8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h313
  let v314 : ℝ := j95.value*j41.value
  have h314 : Bounds (-474252412435075855184351505445249114799/10000000000000000000000000000000000000000 : ℝ) v314 (-118563103108768963796087876354312476449/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v315 : ℝ := j95.tangent*j41.value
  have h315 : Bounds (-1013259217307587937118134772589451337219/2500000000000000000000000000000000000000 : ℝ) v315 (-4053036869230351748472539090312354307167/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v316 : ℝ := j95.value*j41.tangent
  have h316 : Bounds (3733818654103673762958193780537941361/1250000000000000000000000000000000000000 : ℝ) v316 (373381865410367376295819378075838087/125000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v317 : ℝ := v315+v316
  have h317 : Bounds (-1005791579999380589592218385028375454497/2500000000000000000000000000000000000000 : ℝ) v317 (-4023166319997522358368873540066287260207/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h315 h316) (by norm_num) (by norm_num)
  obtain ⟨j96,hj96⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j41=z := ⟨_,rfl⟩
  have j96_value : Bounds (-474252412435075855184351505445249114799/10000000000000000000000000000000000000000 : ℝ) j96.value (-118563103108768963796087876354312476449/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h314
  have j96_tangent : Bounds (-1005791579999380589592218385028375454497/2500000000000000000000000000000000000000 : ℝ) j96.tangent (-4023166319997522358368873540066287260207/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h317
  let v318 : ℝ := j83.value*j85.value
  have h318 : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) v318 (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j83_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v319 : ℝ := j83.tangent*j85.value
  have h319 : Bounds (-71429550511381429634140388856170654297/10000000000000000000000000000000000000000 : ℝ) v319 (-71429550511381429634140388855932617187/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j83_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v320 : ℝ := j83.value*j85.tangent
  have h320 : Bounds (0 : ℝ) v320 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v321 : ℝ := v319+v320
  have h321 : Bounds (-71429550511381429634140388856170654297/10000000000000000000000000000000000000000 : ℝ) v321 (-71429550511381429634140388855932617187/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h319 h320) (by norm_num) (by norm_num)
  obtain ⟨j97,hj97⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j85=z := ⟨_,rfl⟩
  have j97_value : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) j97.value (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h318
  have j97_tangent : Bounds (-71429550511381429634140388856170654297/10000000000000000000000000000000000000000 : ℝ) j97.tangent (-71429550511381429634140388855932617187/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h321
  let v322 : ℝ := j92.value*j97.value
  have h322 : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) v322 (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v323 : ℝ := j92.tangent*j97.value
  have h323 : Bounds (-5013828019302255180125632881040194510851/10000000000000000000000000000000000000000 : ℝ) v323 (-5013828019302255180125632880975736446829/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v324 : ℝ := j92.value*j97.tangent
  have h324 : Bounds (-95585757545054048331729760784886162533/2000000000000000000000000000000000000000 : ℝ) v324 (-477928787725270241658648803921498432893/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j97_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v325 : ℝ := v323+v324
  have h325 : Bounds (-1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) v325 (-2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h323 h324) (by norm_num) (by norm_num)
  obtain ⟨j98,hj98⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j97=z := ⟨_,rfl⟩
  have j98_value : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) j98.value (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h322
  have j98_tangent : Bounds (-1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) j98.tangent (-2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h325
  let v326 : ℝ := -j98.value
  have h326 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v326 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_value) (by norm_num) (by norm_num)
  let v327 : ℝ := j6.value+v326
  have h327 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v327 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h326) (by norm_num) (by norm_num)
  let v328 : ℝ := -j98.tangent
  have h328 : Bounds (2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) v328 (1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_tangent) (by norm_num) (by norm_num)
  let v329 : ℝ := j6.tangent+v328
  have h329 : Bounds (2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) v329 (1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h328) (by norm_num) (by norm_num)
  obtain ⟨j99,hj99⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j98=z := ⟨_,rfl⟩
  have j99_value : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) j99.value (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h327
  have j99_tangent : Bounds (2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) j99.tangent (1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h329
  let v330 : ℝ := j99.value*j70.value
  have h330 : Bounds (-1823826804119871414983425423629889219/39062500000000000000000000000000000000 : ℝ) v330 (-466899661854687082235756908446386930599/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v331 : ℝ := j99.tangent*j70.value
  have h331 : Bounds (-2145217502745127117884485033189306767/62500000000000000000000000000000000000 : ℝ) v331 (-171617400219610169430758802653038589991/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v332 : ℝ := j99.value*j70.tangent
  have h332 : Bounds (3793559752569332543165524881126893811119/10000000000000000000000000000000000000000 : ℝ) v332 (23709748453558328394784530507188559847/62500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v333 : ℝ := v331+v332
  have h333 : Bounds (3450324952130112204304007275816604728399/10000000000000000000000000000000000000000 : ℝ) v333 (1725162476065056102152003637922046197769/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h331 h332) (by norm_num) (by norm_num)
  obtain ⟨j100,hj100⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j70=z := ⟨_,rfl⟩
  have j100_value : Bounds (-1823826804119871414983425423629889219/39062500000000000000000000000000000000 : ℝ) j100.value (-466899661854687082235756908446386930599/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h330
  have j100_tangent : Bounds (3450324952130112204304007275816604728399/10000000000000000000000000000000000000000 : ℝ) j100.tangent (1725162476065056102152003637922046197769/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h333
  let v334 : ℝ := j96.value+j100.value
  have h334 : Bounds (-941152074289762937420108413894500754863/10000000000000000000000000000000000000000 : ℝ) v334 (-188230414857952587484021682772727367279/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_value j100_value) (by norm_num) (by norm_num)
  let v335 : ℝ := j96.tangent+j100.tangent
  have h335 : Bounds (-572841367867410154064866264296897089589/10000000000000000000000000000000000000000 : ℝ) v335 (-572841367867410154064866264222194864669/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_tangent j100_tangent) (by norm_num) (by norm_num)
  obtain ⟨j101,hj101⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j96 j100=z := ⟨_,rfl⟩
  have j101_value : Bounds (-941152074289762937420108413894500754863/10000000000000000000000000000000000000000 : ℝ) j101.value (-188230414857952587484021682772727367279/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h334
  have j101_tangent : Bounds (-572841367867410154064866264296897089589/10000000000000000000000000000000000000000 : ℝ) j101.tangent (-572841367867410154064866264222194864669/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h335
  let v336 : ℝ := j92.value*j84.value
  have h336 : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) v336 (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v337 : ℝ := j92.tangent*j84.value
  have h337 : Bounds (7343260677199062337029587973690251079207/10000000000000000000000000000000000000000 : ℝ) v337 (7343260677199062337029587973776893691257/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v338 : ℝ := j92.value*j84.tangent
  have h338 : Bounds (174993820085835283201847206422326188793/2500000000000000000000000000000000000000 : ℝ) v338 (27999011213733645312295553027714382369/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j84_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v339 : ℝ := v337+v338
  have h339 : Bounds (8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) v339 (4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h337 h338) (by norm_num) (by norm_num)
  obtain ⟨j102,hj102⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j84=z := ⟨_,rfl⟩
  have j102_value : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) j102.value (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h336
  have j102_tangent : Bounds (8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) j102.tangent (4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h339
  let v340 : ℝ := -j102.value
  have h340 : Bounds (-21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v340 (-10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_value) (by norm_num) (by norm_num)
  let v341 : ℝ := j0.value+v340
  have h341 : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v341 (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h340) (by norm_num) (by norm_num)
  let v342 : ℝ := -j102.tangent
  have h342 : Bounds (-4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) v342 (-8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_tangent) (by norm_num) (by norm_num)
  let v343 : ℝ := j0.tangent+v342
  have h343 : Bounds (-4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) v343 (-8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h342) (by norm_num) (by norm_num)
  obtain ⟨j103,hj103⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j102=z := ⟨_,rfl⟩
  have j103_value : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) j103.value (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h341
  have j103_tangent : Bounds (-4021617978771201734918488399734876625241/5000000000000000000000000000000000000000 : ℝ) j103.tangent (-8043235957542403469836976799379555834379/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h343
  let v344 : ℝ := j101.value*j103.value
  have h344 : Bounds (88576722693992345512649704591593057051/10000000000000000000000000000000000000000 : ℝ) v344 (88576722693992345512649704599727268807/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v345 : ℝ := j101.tangent*j103.value
  have h345 : Bounds (53913084160739822093582208637398790549/10000000000000000000000000000000000000000 : ℝ) v345 (53913084160739822093582208647612360151/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v346 : ℝ := j101.value*j103.tangent
  have h346 : Bounds (378495410272152032300119619426950677699/5000000000000000000000000000000000000000 : ℝ) v346 (378495410272152032300119619443607440903/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v347 : ℝ := v345+v346
  have h347 : Bounds (810903904705043886693821447491300145947/10000000000000000000000000000000000000000 : ℝ) v347 (810903904705043886693821447534827241957/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h345 h346) (by norm_num) (by norm_num)
  obtain ⟨j104,hj104⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j103=z := ⟨_,rfl⟩
  have j104_value : Bounds (88576722693992345512649704591593057051/10000000000000000000000000000000000000000 : ℝ) j104.value (88576722693992345512649704599727268807/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h344
  have j104_tangent : Bounds (810903904705043886693821447491300145947/10000000000000000000000000000000000000000 : ℝ) j104.tangent (810903904705043886693821447534827241957/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h347
  let v348 : ℝ := j95.value*j52.value
  have h348 : Bounds (3676375290194386474297298491606588417/625000000000000000000000000000000000000 : ℝ) v348 (29411002321555091794378387934589092391/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v349 : ℝ := j95.tangent*j52.value
  have h349 : Bounds (15709445229575006777025345311288194989/312500000000000000000000000000000000000 : ℝ) v349 (125675561836600054216202762491714894539/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v350 : ℝ := j95.value*j52.tangent
  have h350 : Bounds (-119482196931317560414662200984268187837/2500000000000000000000000000000000000000 : ℝ) v350 (-477928787725270241658648803908856494213/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v351 : ℝ := v349+v350
  have h351 : Bounds (247734596211299752061622460241494883/100000000000000000000000000000000000000 : ℝ) v351 (24773459621129975206162246058003083943/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h349 h350) (by norm_num) (by norm_num)
  obtain ⟨j105,hj105⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j52=z := ⟨_,rfl⟩
  have j105_value : Bounds (3676375290194386474297298491606588417/625000000000000000000000000000000000000 : ℝ) j105.value (29411002321555091794378387934589092391/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h348
  have j105_tangent : Bounds (247734596211299752061622460241494883/100000000000000000000000000000000000000 : ℝ) j105.tangent (24773459621129975206162246058003083943/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h351
  let v352 : ℝ := j99.value*j76.value
  have h352 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v352 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v353 : ℝ := j99.tangent*j76.value
  have h353 : Bounds (2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) v353 (1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v354 : ℝ := j99.value*j76.tangent
  have h354 : Bounds (-1823826804119871414983425423629889219/19531250000000000000000000000000000000 : ℝ) v354 (-466899661854687082235756908446386930599/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v355 : ℝ := v353+v354
  have h355 : Bounds (2278978741659075628656383933999365799797/5000000000000000000000000000000000000000 : ℝ) v355 (2278978741659075628656383934035925731159/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h353 h354) (by norm_num) (by norm_num)
  obtain ⟨j106,hj106⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j76=z := ⟨_,rfl⟩
  have j106_value : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) j106.value (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h352
  have j106_tangent : Bounds (2278978741659075628656383933999365799797/5000000000000000000000000000000000000000 : ℝ) j106.tangent (2278978741659075628656383934035925731159/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h355
  let v356 : ℝ := j105.value+j106.value
  have h356 : Bounds (3764608297159051749680433655503948152131/5000000000000000000000000000000000000000 : ℝ) v356 (1505843318863620699872173462211440885161/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_value j106_value) (by norm_num) (by norm_num)
  let v357 : ℝ := j105.tangent+j106.tangent
  have h357 : Bounds (2291365471469640616259465057011440543947/5000000000000000000000000000000000000000 : ℝ) v357 (4582730942939281232518930114129854546261/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_tangent j106_tangent) (by norm_num) (by norm_num)
  obtain ⟨j107,hj107⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j105 j106=z := ⟨_,rfl⟩
  have j107_value : Bounds (3764608297159051749680433655503948152131/5000000000000000000000000000000000000000 : ℝ) j107.value (1505843318863620699872173462211440885161/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h356
  have j107_tangent : Bounds (2291365471469640616259465057011440543947/5000000000000000000000000000000000000000 : ℝ) j107.tangent (4582730942939281232518930114129854546261/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h357
  let v358 : ℝ := j85.value*j83.value
  have h358 : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) v358 (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v359 : ℝ := j85.tangent*j83.value
  have h359 : Bounds (0 : ℝ) v359 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v360 : ℝ := j85.value*j83.tangent
  have h360 : Bounds (-71429550511381429634140388856170654297/10000000000000000000000000000000000000000 : ℝ) v360 (-71429550511381429634140388855932617187/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v361 : ℝ := v359+v360
  have h361 : Bounds (-71429550511381429634140388856170654297/10000000000000000000000000000000000000000 : ℝ) v361 (-71429550511381429634140388855932617187/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h359 h360) (by norm_num) (by norm_num)
  obtain ⟨j108,hj108⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j83=z := ⟨_,rfl⟩
  have j108_value : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) j108.value (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h358
  have j108_tangent : Bounds (-71429550511381429634140388856170654297/10000000000000000000000000000000000000000 : ℝ) j108.tangent (-71429550511381429634140388855932617187/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h361
  let v362 : ℝ := j92.value*j108.value
  have h362 : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) v362 (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v363 : ℝ := j92.tangent*j108.value
  have h363 : Bounds (-5013828019302255180125632881040194510851/10000000000000000000000000000000000000000 : ℝ) v363 (-5013828019302255180125632880975736446829/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v364 : ℝ := j92.value*j108.tangent
  have h364 : Bounds (-95585757545054048331729760784886162533/2000000000000000000000000000000000000000 : ℝ) v364 (-477928787725270241658648803921498432893/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j108_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v365 : ℝ := v363+v364
  have h365 : Bounds (-1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) v365 (-2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h363 h364) (by norm_num) (by norm_num)
  obtain ⟨j109,hj109⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j108=z := ⟨_,rfl⟩
  have j109_value : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) j109.value (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h362
  have j109_tangent : Bounds (-1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) j109.tangent (-2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h365
  let v366 : ℝ := -j109.value
  have h366 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v366 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_value) (by norm_num) (by norm_num)
  let v367 : ℝ := j6.value+v366
  have h367 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v367 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h366) (by norm_num) (by norm_num)
  let v368 : ℝ := -j109.tangent
  have h368 : Bounds (2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) v368 (1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_tangent) (by norm_num) (by norm_num)
  let v369 : ℝ := j6.tangent+v368
  have h369 : Bounds (2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) v369 (1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h368) (by norm_num) (by norm_num)
  obtain ⟨j110,hj110⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j109=z := ⟨_,rfl⟩
  have j110_value : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) j110.value (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h367
  have j110_tangent : Bounds (2745878403513762710892140842448617439861/5000000000000000000000000000000000000000 : ℝ) j110.tangent (1372939201756881355446070421241156330879/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h369
  let v370 : ℝ := j107.value*j110.value
  have h370 : Bounds (562462189106851394005325624178874757537/1000000000000000000000000000000000000000 : ℝ) v370 (5624621891068513940053256241860093116673/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v371 : ℝ := j107.tangent*j110.value
  have h371 : Bounds (3423480844206978702942470248748644783359/10000000000000000000000000000000000000000 : ℝ) v371 (427935105525872337867808781106195410769/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v372 : ℝ := j107.value*j110.tangent
  have h372 : Bounds (4134862648343104727840938188794090445291/10000000000000000000000000000000000000000 : ℝ) v372 (165394505933724189113637527554876359651/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v373 : ℝ := v371+v372
  have h373 : Bounds (151166869851001668615668168750854704573/200000000000000000000000000000000000000 : ℝ) v373 (7558343492550083430783408437721472277427/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h371 h372) (by norm_num) (by norm_num)
  obtain ⟨j111,hj111⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j110=z := ⟨_,rfl⟩
  have j111_value : Bounds (562462189106851394005325624178874757537/1000000000000000000000000000000000000000 : ℝ) j111.value (5624621891068513940053256241860093116673/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h370
  have j111_tangent : Bounds (151166869851001668615668168750854704573/200000000000000000000000000000000000000 : ℝ) j111.tangent (7558343492550083430783408437721472277427/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h373
  let v374 : ℝ := j104.value+j111.value
  have h374 : Bounds (5713198613762506285565905946380340632421/10000000000000000000000000000000000000000 : ℝ) v374 (142829965344062657139147648661495509637/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_value j111_value) (by norm_num) (by norm_num)
  let v375 : ℝ := j104.tangent+j111.tangent
  have h375 : Bounds (8369247397255127317477229885034035374597/10000000000000000000000000000000000000000 : ℝ) v375 (1046155924656890914684653735657037439923/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_tangent j111_tangent) (by norm_num) (by norm_num)
  obtain ⟨j112,hj112⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j104 j111=z := ⟨_,rfl⟩
  have j112_value : Bounds (5713198613762506285565905946380340632421/10000000000000000000000000000000000000000 : ℝ) j112.value (142829965344062657139147648661495509637/250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj112,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h374
  have j112_tangent : Bounds (8369247397255127317477229885034035374597/10000000000000000000000000000000000000000 : ℝ) j112.tangent (1046155924656890914684653735657037439923/1250000000000000000000000000000000000000 : ℝ) := by
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
  have h380 : Bounds (205836693946580961938127702138914652069/2000000000000000000000000000000000000000 : ℝ) v380 (1029183469732904809690638510697458191219/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v381 : ℝ := j92.tangent*j113.value
  have h381 : Bounds (8634331251861706955978637088751618931/125000000000000000000000000000000000000 : ℝ) v381 (21585828129654267389946592722084621779/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v382 : ℝ := j92.value*j113.tangent
  have h382 : Bounds (65843430642361036053042818105459903467/5000000000000000000000000000000000000000 : ℝ) v382 (13168686128472207210608563621128894179/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j113_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v383 : ℝ := v381+v382
  have h383 : Bounds (411216680716829314292188301655524660707/5000000000000000000000000000000000000000 : ℝ) v383 (411216680716829314292188301658998419359/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h381 h382) (by norm_num) (by norm_num)
  obtain ⟨j114,hj114⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j113=z := ⟨_,rfl⟩
  have j114_value : Bounds (205836693946580961938127702138914652069/2000000000000000000000000000000000000000 : ℝ) j114.value (1029183469732904809690638510697458191219/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h380
  have j114_tangent : Bounds (411216680716829314292188301655524660707/5000000000000000000000000000000000000000 : ℝ) j114.tangent (411216680716829314292188301658998419359/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h383
  let v384 : ℝ := j112.value+j114.value
  have h384 : Bounds (3371191041747705547628272228537456946383/5000000000000000000000000000000000000000 : ℝ) v384 (6742382083495411095256544457157278576699/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_value j114_value) (by norm_num) (by norm_num)
  let v385 : ℝ := j112.tangent+j114.tangent
  have h385 : Bounds (9191680758688785946061606488345084696011/10000000000000000000000000000000000000000 : ℝ) v385 (4595840379344392973030803244287148179051/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_tangent j114_tangent) (by norm_num) (by norm_num)
  obtain ⟨j115,hj115⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j112 j114=z := ⟨_,rfl⟩
  have j115_value : Bounds (3371191041747705547628272228537456946383/5000000000000000000000000000000000000000 : ℝ) j115.value (6742382083495411095256544457157278576699/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h384
  have j115_tangent : Bounds (9191680758688785946061606488345084696011/10000000000000000000000000000000000000000 : ℝ) j115.tangent (4595840379344392973030803244287148179051/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h385
  let v386 : ℝ := j77.value*j89.value
  have h386 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v386 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v387 : ℝ := j77.tangent*j89.value
  have h387 : Bounds (0 : ℝ) v387 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v388 : ℝ := j77.value*j89.tangent
  have h388 : Bounds (83064329940508473730726432687563/512000000000000000000000000000000 : ℝ) v388 (10383041242563559216340804085969/64000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v389 : ℝ := v387+v388
  have h389 : Bounds (83064329940508473730726432687563/512000000000000000000000000000000 : ℝ) v389 (10383041242563559216340804085969/64000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h387 h388) (by norm_num) (by norm_num)
  obtain ⟨j116,hj116⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j89=z := ⟨_,rfl⟩
  have j116_value : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) j116.value (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h386
  have j116_tangent : Bounds (83064329940508473730726432687563/512000000000000000000000000000000 : ℝ) j116.tangent (10383041242563559216340804085969/64000000000000000000000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h389
  let v390 : ℝ := j92.value*j116.value
  have h390 : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) v390 (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v391 : ℝ := j92.tangent*j116.value
  have h391 : Bounds (231283800856663380693845290509929167849/2500000000000000000000000000000000000000 : ℝ) v391 (28910475107082922586730661314082258627/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v392 : ℝ := j92.value*j116.tangent
  have h392 : Bounds (10855001270555197874920737481458756818737/10000000000000000000000000000000000000000 : ℝ) v392 (10855001270555197874920737481513883626133/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v393 : ℝ := v391+v392
  have h393 : Bounds (11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) v393 (11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h391 h392) (by norm_num) (by norm_num)
  obtain ⟨j117,hj117⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j116=z := ⟨_,rfl⟩
  have j117_value : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) j117.value (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h390
  have j117_tangent : Bounds (11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) j117.tangent (11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h393
  let v394 : ℝ := -j117.value
  have h394 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v394 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_value) (by norm_num) (by norm_num)
  let v395 : ℝ := j6.value+v394
  have h395 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v395 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h394) (by norm_num) (by norm_num)
  let v396 : ℝ := -j117.tangent
  have h396 : Bounds (-11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) v396 (-11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_tangent) (by norm_num) (by norm_num)
  let v397 : ℝ := j6.tangent+v396
  have h397 : Bounds (-11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) v397 (-11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h396) (by norm_num) (by norm_num)
  obtain ⟨j118,hj118⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j117=z := ⟨_,rfl⟩
  have j118_value : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) j118.value (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h395
  have j118_tangent : Bounds (-11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) j118.tangent (-11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h397
  let v398 : ℝ := j101.value*j118.value
  have h398 : Bounds (2027025190912904100261334878848877743/156250000000000000000000000000000000000 : ℝ) v398 (129729612218425862416725432251241325817/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v399 : ℝ := j101.tangent*j118.value
  have h399 : Bounds (39480595403348029994232974668320860171/5000000000000000000000000000000000000000 : ℝ) v399 (19740297701674014997116487336834943299/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v400 : ℝ := j101.value*j118.tangent
  have h400 : Bounds (1108689987790451342921224067795432849089/10000000000000000000000000000000000000000 : ℝ) v400 (34646562118451604466288252119937705049/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v401 : ℝ := v399+v400
  have h401 : Bounds (1187651178597147402909690017132074569431/10000000000000000000000000000000000000000 : ℝ) v401 (296912794649286850727422504296336583691/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h399 h400) (by norm_num) (by norm_num)
  obtain ⟨j119,hj119⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j118=z := ⟨_,rfl⟩
  have j119_value : Bounds (2027025190912904100261334878848877743/156250000000000000000000000000000000000 : ℝ) j119.value (129729612218425862416725432251241325817/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h398
  have j119_tangent : Bounds (1187651178597147402909690017132074569431/10000000000000000000000000000000000000000 : ℝ) j119.tangent (296912794649286850727422504296336583691/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h401
  let v402 : ℝ := j92.value*j90.value
  have h402 : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) v402 (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v403 : ℝ := j92.tangent*j90.value
  have h403 : Bounds (-78957921563815042206702880016381015919/1250000000000000000000000000000000000000 : ℝ) v403 (-157915843127630084413405760030731856593/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v404 : ℝ := j92.value*j90.tangent
  have h404 : Bounds (-7411572585031883132183353759320403987157/10000000000000000000000000000000000000000 : ℝ) v404 (-7411572585031883132183353759274929544003/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v405 : ℝ := v403+v404
  have h405 : Bounds (-8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) v405 (-64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h403 h404) (by norm_num) (by norm_num)
  obtain ⟨j120,hj120⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j90=z := ⟨_,rfl⟩
  have j120_value : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) j120.value (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h402
  have j120_tangent : Bounds (-8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) j120.tangent (-64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h405
  let v406 : ℝ := -j120.value
  have h406 : Bounds (941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v406 (470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_value) (by norm_num) (by norm_num)
  let v407 : ℝ := j0.value+v406
  have h407 : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v407 (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h406) (by norm_num) (by norm_num)
  let v408 : ℝ := -j120.tangent
  have h408 : Bounds (64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) v408 (8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_tangent) (by norm_num) (by norm_num)
  let v409 : ℝ := j0.tangent+v408
  have h409 : Bounds (64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) v409 (8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h408) (by norm_num) (by norm_num)
  obtain ⟨j121,hj121⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j120=z := ⟨_,rfl⟩
  have j121_value : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) j121.value (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h407
  have j121_tangent : Bounds (64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) j121.tangent (8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h409
  let v410 : ℝ := j107.value*j121.value
  have h410 : Bounds (8237830375870042263462064947768683400371/10000000000000000000000000000000000000000 : ℝ) v410 (1029728796983755282932758118478372492071/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v411 : ℝ := j107.tangent*j121.value
  have h411 : Bounds (1002807123245039961853517556631313723931/2000000000000000000000000000000000000000 : ℝ) v411 (1253508904056299952316896945819064055027/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v412 : ℝ := j107.value*j121.tangent
  have h412 : Bounds (3027963282177216258400956955462229316793/5000000000000000000000000000000000000000 : ℝ) v412 (1211185312870886503360382782200894252813/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v413 : ℝ := v411+v412
  have h413 : Bounds (11069962180579632326069501694081027253241/10000000000000000000000000000000000000000 : ℝ) v413 (11069962180579632326069501694280727484173/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h411 h412) (by norm_num) (by norm_num)
  obtain ⟨j122,hj122⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j121=z := ⟨_,rfl⟩
  have j122_value : Bounds (8237830375870042263462064947768683400371/10000000000000000000000000000000000000000 : ℝ) j122.value (1029728796983755282932758118478372492071/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h410
  have j122_tangent : Bounds (11069962180579632326069501694081027253241/10000000000000000000000000000000000000000 : ℝ) j122.tangent (11069962180579632326069501694280727484173/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h413
  let v414 : ℝ := j119.value+j122.value
  have h414 : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) v414 (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_value j122_value) (by norm_num) (by norm_num)
  let v415 : ℝ := j119.tangent+j122.tangent
  have h415 : Bounds (766100834948548733061199481950818863917/625000000000000000000000000000000000000 : ℝ) v415 (12257613359176779728979191711466073818937/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_tangent j122_tangent) (by norm_num) (by norm_num)
  obtain ⟨j123,hj123⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j119 j122=z := ⟨_,rfl⟩
  have j123_value : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) j123.value (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj123,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h414
  have j123_tangent : Bounds (766100834948548733061199481950818863917/625000000000000000000000000000000000000 : ℝ) j123.tangent (12257613359176779728979191711466073818937/10000000000000000000000000000000000000000 : ℝ) := by
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
  have h420 : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) v420 (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v421 : ℝ := j92.tangent*j124.value
  have h421 : Bounds (87023181121125865383091775382693482139/10000000000000000000000000000000000000000 : ℝ) v421 (21755795280281466345772943845880563683/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v422 : ℝ := j92.value*j124.tangent
  have h422 : Bounds (1029374898241132146439914468009477080779/10000000000000000000000000000000000000000 : ℝ) v422 (1029374898241132146439914468012362548251/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v423 : ℝ := v421+v422
  have h423 : Bounds (558199039681129005911503121696085281459/5000000000000000000000000000000000000000 : ℝ) v423 (1116398079362258011823006243395884802983/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h421 h422) (by norm_num) (by norm_num)
  obtain ⟨j125,hj125⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j124=z := ⟨_,rfl⟩
  have j125_value : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) j125.value (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h420
  have j125_tangent : Bounds (558199039681129005911503121696085281459/5000000000000000000000000000000000000000 : ℝ) j125.tangent (1116398079362258011823006243395884802983/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h423
  let v424 : ℝ := j123.value+j125.value
  have h424 : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) v424 (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_value j125_value) (by norm_num) (by norm_num)
  let v425 : ℝ := j123.tangent+j125.tangent
  have h425 : Bounds (1337401143853903774080219795460527238559/1000000000000000000000000000000000000000 : ℝ) v425 (83587571490868985880013737217887241387/62500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_tangent j125_tangent) (by norm_num) (by norm_num)
  obtain ⟨j126,hj126⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j123 j125=z := ⟨_,rfl⟩
  have j126_value : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) j126.value (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h424
  have j126_tangent : Bounds (1337401143853903774080219795460527238559/1000000000000000000000000000000000000000 : ℝ) j126.tangent (83587571490868985880013737217887241387/62500000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h425
  let v426 : ℝ := j89.value*j77.value
  have h426 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v426 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v427 : ℝ := j89.tangent*j77.value
  have h427 : Bounds (83064329940508473730726432687563/512000000000000000000000000000000 : ℝ) v427 (10383041242563559216340804085969/64000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v428 : ℝ := j89.value*j77.tangent
  have h428 : Bounds (0 : ℝ) v428 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v429 : ℝ := v427+v428
  have h429 : Bounds (83064329940508473730726432687563/512000000000000000000000000000000 : ℝ) v429 (10383041242563559216340804085969/64000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h427 h428) (by norm_num) (by norm_num)
  obtain ⟨j127,hj127⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j77=z := ⟨_,rfl⟩
  have j127_value : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) j127.value (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h426
  have j127_tangent : Bounds (83064329940508473730726432687563/512000000000000000000000000000000 : ℝ) j127.tangent (10383041242563559216340804085969/64000000000000000000000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h429
  let v430 : ℝ := j92.value*j127.value
  have h430 : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) v430 (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v431 : ℝ := j92.tangent*j127.value
  have h431 : Bounds (231283800856663380693845290509929167849/2500000000000000000000000000000000000000 : ℝ) v431 (28910475107082922586730661314082258627/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v432 : ℝ := j92.value*j127.tangent
  have h432 : Bounds (10855001270555197874920737481458756818737/10000000000000000000000000000000000000000 : ℝ) v432 (10855001270555197874920737481513883626133/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v433 : ℝ := v431+v432
  have h433 : Bounds (11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) v433 (11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h431 h432) (by norm_num) (by norm_num)
  obtain ⟨j128,hj128⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j127=z := ⟨_,rfl⟩
  have j128_value : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) j128.value (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h430
  have j128_tangent : Bounds (11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) j128.tangent (11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h433
  let v434 : ℝ := -j128.value
  have h434 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v434 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_value) (by norm_num) (by norm_num)
  let v435 : ℝ := j6.value+v434
  have h435 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v435 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h434) (by norm_num) (by norm_num)
  let v436 : ℝ := -j128.tangent
  have h436 : Bounds (-11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) v436 (-11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_tangent) (by norm_num) (by norm_num)
  let v437 : ℝ := j6.tangent+v436
  have h437 : Bounds (-11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) v437 (-11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h436) (by norm_num) (by norm_num)
  obtain ⟨j129,hj129⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j128=z := ⟨_,rfl⟩
  have j129_value : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) j129.value (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h435
  have j129_tangent : Bounds (-11780136473981851397696118643564515902197/10000000000000000000000000000000000000000 : ℝ) j129.tangent (-11780136473981851397696118643498473490133/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h437
  let v438 : ℝ := j129.value*j41.value
  have h438 : Bounds (-347295427554965408200589071209149550539/5000000000000000000000000000000000000000 : ℝ) v438 (-347295427554965408200589071207385820837/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v439 : ℝ := j129.tangent*j41.value
  have h439 : Bounds (-2968042197546208652935154892616840920671/5000000000000000000000000000000000000000 : ℝ) v439 (-5936084395092417305870309785200402657137/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v440 : ℝ := j129.value*j41.tangent
  have h440 : Bounds (21874227510729410400230900802790773599/5000000000000000000000000000000000000000 : ℝ) v440 (10937113755364705200115450401450930613/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v441 : ℝ := v439+v440
  have h441 : Bounds (-11508468632951090791152046843023633387/19531250000000000000000000000000000000 : ℝ) v441 (-1178467188014191697013969596718919786937/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h439 h440) (by norm_num) (by norm_num)
  obtain ⟨j130,hj130⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j41=z := ⟨_,rfl⟩
  have j130_value : Bounds (-347295427554965408200589071209149550539/5000000000000000000000000000000000000000 : ℝ) j130.value (-347295427554965408200589071207385820837/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h438
  have j130_tangent : Bounds (-11508468632951090791152046843023633387/19531250000000000000000000000000000000 : ℝ) j130.tangent (-1178467188014191697013969596718919786937/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h441
  let v442 : ℝ := j89.value*j85.value
  have h442 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v442 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v443 : ℝ := j89.tangent*j85.value
  have h443 : Bounds (-11342924707914433941065020962189/102400000000000000000000000000000 : ℝ) v443 (-14178655884893042426331276202689/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v444 : ℝ := j89.value*j85.tangent
  have h444 : Bounds (0 : ℝ) v444 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v445 : ℝ := v443+v444
  have h445 : Bounds (-11342924707914433941065020962189/102400000000000000000000000000000 : ℝ) v445 (-14178655884893042426331276202689/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h443 h444) (by norm_num) (by norm_num)
  obtain ⟨j131,hj131⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j85=z := ⟨_,rfl⟩
  have j131_value : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) j131.value (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h442
  have j131_tangent : Bounds (-11342924707914433941065020962189/102400000000000000000000000000000 : ℝ) j131.tangent (-14178655884893042426331276202689/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h445
  let v446 : ℝ := j92.value*j131.value
  have h446 : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) v446 (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v447 : ℝ := j92.tangent*j131.value
  have h447 : Bounds (-78957921563815042206702880016381015919/1250000000000000000000000000000000000000 : ℝ) v447 (-157915843127630084413405760030731856593/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v448 : ℝ := j92.value*j131.tangent
  have h448 : Bounds (-7411572585031883132183353759320403987157/10000000000000000000000000000000000000000 : ℝ) v448 (-7411572585031883132183353759274929544003/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v449 : ℝ := v447+v448
  have h449 : Bounds (-8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) v449 (-64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h447 h448) (by norm_num) (by norm_num)
  obtain ⟨j132,hj132⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j131=z := ⟨_,rfl⟩
  have j132_value : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) j132.value (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h446
  have j132_tangent : Bounds (-8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) j132.tangent (-64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h449
  let v450 : ℝ := -j132.value
  have h450 : Bounds (941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v450 (470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_value) (by norm_num) (by norm_num)
  let v451 : ℝ := j0.value+v450
  have h451 : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v451 (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h450) (by norm_num) (by norm_num)
  let v452 : ℝ := -j132.tangent
  have h452 : Bounds (64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) v452 (8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_tangent) (by norm_num) (by norm_num)
  let v453 : ℝ := j0.tangent+v452
  have h453 : Bounds (64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) v453 (8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h452) (by norm_num) (by norm_num)
  obtain ⟨j133,hj133⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j132=z := ⟨_,rfl⟩
  have j133_value : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) j133.value (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h451
  have j133_tangent : Bounds (64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) j133.tangent (8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h453
  let v454 : ℝ := j133.value*j70.value
  have h454 : Bounds (-683822004643110183588756775867622253867/10000000000000000000000000000000000000000 : ℝ) v454 (-683822004643110183588756775867261345587/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v455 : ℝ := j133.tangent*j70.value
  have h455 : Bounds (-502702247346400216864811049965715757157/10000000000000000000000000000000000000000 : ℝ) v455 (-62837780918300027108101381245295757581/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v456 : ℝ := j133.value*j70.tangent
  have h456 : Bounds (43406670216603673762958193780636706507/78125000000000000000000000000000000000 : ℝ) v456 (1111210757545054048331729760784886162533/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v457 : ℝ := v455+v456
  have h457 : Bounds (5053351540378870024793837753955782675739/10000000000000000000000000000000000000000 : ℝ) v457 (5053351540378870024793837753962064752017/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h455 h456) (by norm_num) (by norm_num)
  obtain ⟨j134,hj134⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j70=z := ⟨_,rfl⟩
  have j134_value : Bounds (-683822004643110183588756775867622253867/10000000000000000000000000000000000000000 : ℝ) j134.value (-683822004643110183588756775867261345587/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h454
  have j134_tangent : Bounds (5053351540378870024793837753955782675739/10000000000000000000000000000000000000000 : ℝ) j134.tangent (5053351540378870024793837753962064752017/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h457
  let v458 : ℝ := j130.value+j134.value
  have h458 : Bounds (-275682571950608199997986983657184270989/2000000000000000000000000000000000000000 : ℝ) v458 (-1378412859753040999989934918282032987261/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_value j134_value) (by norm_num) (by norm_num)
  let v459 : ℝ := j130.tangent+j134.tangent
  have h459 : Bounds (-167796879938417692055202045934463523681/2000000000000000000000000000000000000000 : ℝ) v459 (-209746099923022115069002557408133545667/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_tangent j134_tangent) (by norm_num) (by norm_num)
  obtain ⟨j135,hj135⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j130 j134=z := ⟨_,rfl⟩
  have j135_value : Bounds (-275682571950608199997986983657184270989/2000000000000000000000000000000000000000 : ℝ) j135.value (-1378412859753040999989934918282032987261/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h458
  have j135_tangent : Bounds (-167796879938417692055202045934463523681/2000000000000000000000000000000000000000 : ℝ) j135.tangent (-209746099923022115069002557408133545667/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h459
  let v460 : ℝ := j135.value*j103.value
  have h460 : Bounds (129729612218425862416725432244772244637/10000000000000000000000000000000000000000 : ℝ) v460 (32432403054606465604181358063199314183/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v461 : ℝ := j135.tangent*j103.value
  have h461 : Bounds (3948059540334802999423297466889387683/500000000000000000000000000000000000000 : ℝ) v461 (1974029770167401499711648733654843497/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v462 : ℝ := j135.value*j103.tangent
  have h462 : Bounds (554344993895225671460612033904469744237/5000000000000000000000000000000000000000 : ℝ) v462 (55434499389522567146061203391224996109/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v463 : ℝ := v461+v462
  have h463 : Bounds (593825589298573701454845008573363621067/5000000000000000000000000000000000000000 : ℝ) v463 (59382558929857370145484500858534683103/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h461 h462) (by norm_num) (by norm_num)
  obtain ⟨j136,hj136⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j103=z := ⟨_,rfl⟩
  have j136_value : Bounds (129729612218425862416725432244772244637/10000000000000000000000000000000000000000 : ℝ) j136.value (32432403054606465604181358063199314183/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h460
  have j136_tangent : Bounds (593825589298573701454845008573363621067/5000000000000000000000000000000000000000 : ℝ) j136.tangent (59382558929857370145484500858534683103/500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h463
  let v464 : ℝ := j129.value*j52.value
  have h464 : Bounds (86150803734565062499370932392529816021/10000000000000000000000000000000000000000 : ℝ) v464 (86150803734565062499370932392967330367/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v465 : ℝ := j129.tangent*j52.value
  have h465 : Bounds (736258529623865712356007415218654593133/10000000000000000000000000000000000000000 : ℝ) v465 (46016158101491607022250463451423890243/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v466 : ℝ := j129.value*j52.tangent
  have h466 : Bounds (-349987640171670566403694412846429779613/5000000000000000000000000000000000000000 : ℝ) v466 (-87496910042917641600923603211163094397/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v467 : ℝ := v465+v466
  have h467 : Bounds (36283249280524579548618589525795033907/10000000000000000000000000000000000000000 : ℝ) v467 (4535406160065572443577323691684686089/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h465 h466) (by norm_num) (by norm_num)
  obtain ⟨j137,hj137⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j52=z := ⟨_,rfl⟩
  have j137_value : Bounds (86150803734565062499370932392529816021/10000000000000000000000000000000000000000 : ℝ) j137.value (86150803734565062499370932392967330367/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h464
  have j137_tangent : Bounds (36283249280524579548618589525795033907/10000000000000000000000000000000000000000 : ℝ) j137.tangent (4535406160065572443577323691684686089/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h467
  let v468 : ℝ := j133.value*j76.value
  have h468 : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v468 (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v469 : ℝ := j133.tangent*j76.value
  have h469 : Bounds (64345887660339227758695814395182855763/80000000000000000000000000000000000000 : ℝ) v469 (8043235957542403469836976799451452114509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v470 : ℝ := j133.value*j76.tangent
  have h470 : Bounds (-1367644009286220367177513551735244507733/10000000000000000000000000000000000000000 : ℝ) v470 (-683822004643110183588756775867261345587/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v471 : ℝ := v469+v470
  have h471 : Bounds (3337795974128091551329731623831306231321/5000000000000000000000000000000000000000 : ℝ) v471 (1335118389651236620531892649543385884667/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h469 h470) (by norm_num) (by norm_num)
  obtain ⟨j138,hj138⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j76=z := ⟨_,rfl⟩
  have j138_value : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) j138.value (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h468
  have j138_tangent : Bounds (3337795974128091551329731623831306231321/5000000000000000000000000000000000000000 : ℝ) j138.tangent (1335118389651236620531892649543385884667/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h471
  let v472 : ℝ := j137.value+j138.value
  have h472 : Bounds (5513651439012163999959739673134355672709/5000000000000000000000000000000000000000 : ℝ) v472 (11027302878024327999919479346274923392229/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_value j138_value) (by norm_num) (by norm_num)
  let v473 : ℝ := j137.tangent+j138.tangent
  have h473 : Bounds (6711875197536707682208081837188407496549/10000000000000000000000000000000000000000 : ℝ) v473 (6711875197536707682208081837250406912047/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_tangent j138_tangent) (by norm_num) (by norm_num)
  obtain ⟨j139,hj139⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j137 j138=z := ⟨_,rfl⟩
  have j139_value : Bounds (5513651439012163999959739673134355672709/5000000000000000000000000000000000000000 : ℝ) j139.value (11027302878024327999919479346274923392229/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h472
  have j139_tangent : Bounds (6711875197536707682208081837188407496549/10000000000000000000000000000000000000000 : ℝ) j139.tangent (6711875197536707682208081837250406912047/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h473
  let v474 : ℝ := j139.value*j110.value
  have h474 : Bounds (4118915187935021131731032473885119665643/5000000000000000000000000000000000000000 : ℝ) v474 (8237830375870042263462064947825424005653/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v475 : ℝ := j139.tangent*j110.value
  have h475 : Bounds (2507017808112599904633793891588936178531/5000000000000000000000000000000000000000 : ℝ) v475 (2507017808112599904633793891627476241359/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v476 : ℝ := j139.value*j110.tangent
  have h476 : Bounds (6055926564354432516801913910925602454559/10000000000000000000000000000000000000000 : ℝ) v476 (1513981641088608129200478477750831860769/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v477 : ℝ := v475+v476
  have h477 : Bounds (11069962180579632326069501694103474811621/10000000000000000000000000000000000000000 : ℝ) v477 (5534981090289816163034750847129139962897/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h475 h476) (by norm_num) (by norm_num)
  obtain ⟨j140,hj140⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j110=z := ⟨_,rfl⟩
  have j140_value : Bounds (4118915187935021131731032473885119665643/5000000000000000000000000000000000000000 : ℝ) j140.value (8237830375870042263462064947825424005653/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h474
  have j140_tangent : Bounds (11069962180579632326069501694103474811621/10000000000000000000000000000000000000000 : ℝ) j140.tangent (5534981090289816163034750847129139962897/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h477
  let v478 : ℝ := j136.value+j140.value
  have h478 : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) v478 (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_value j140_value) (by norm_num) (by norm_num)
  let v479 : ℝ := j136.tangent+j140.tangent
  have h479 : Bounds (2451522671835355945795838342250040410751/2000000000000000000000000000000000000000 : ℝ) v479 (6128806679588389864489595855714486793927/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_tangent j140_tangent) (by norm_num) (by norm_num)
  obtain ⟨j141,hj141⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j136 j140=z := ⟨_,rfl⟩
  have j141_value : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) j141.value (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj141,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h478
  have j141_tangent : Bounds (2451522671835355945795838342250040410751/2000000000000000000000000000000000000000 : ℝ) j141.tangent (6128806679588389864489595855714486793927/5000000000000000000000000000000000000000 : ℝ) := by
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
  have h484 : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) v484 (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v485 : ℝ := j92.tangent*j142.value
  have h485 : Bounds (87023181121125865383091775382693482139/10000000000000000000000000000000000000000 : ℝ) v485 (21755795280281466345772943845880563683/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v486 : ℝ := j92.value*j142.tangent
  have h486 : Bounds (1029374898241132146439914468009477080779/10000000000000000000000000000000000000000 : ℝ) v486 (1029374898241132146439914468012362548251/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v487 : ℝ := v485+v486
  have h487 : Bounds (558199039681129005911503121696085281459/5000000000000000000000000000000000000000 : ℝ) v487 (1116398079362258011823006243395884802983/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h485 h486) (by norm_num) (by norm_num)
  obtain ⟨j143,hj143⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j142=z := ⟨_,rfl⟩
  have j143_value : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) j143.value (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h484
  have j143_tangent : Bounds (558199039681129005911503121696085281459/5000000000000000000000000000000000000000 : ℝ) j143.tangent (1116398079362258011823006243395884802983/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h487
  let v488 : ℝ := j141.value+j143.value
  have h488 : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) v488 (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_value j143_value) (by norm_num) (by norm_num)
  let v489 : ℝ := j141.tangent+j143.tangent
  have h489 : Bounds (13374011438539037740802197954642372616673/10000000000000000000000000000000000000000 : ℝ) v489 (13374011438539037740802197954824858390837/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_tangent j143_tangent) (by norm_num) (by norm_num)
  obtain ⟨j144,hj144⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j141 j143=z := ⟨_,rfl⟩
  have j144_value : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) j144.value (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h488
  have j144_tangent : Bounds (13374011438539037740802197954642372616673/10000000000000000000000000000000000000000 : ℝ) j144.tangent (13374011438539037740802197954824858390837/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h489
  let v490 : ℝ := j135.value*j118.value
  have h490 : Bounds (95001100596627833852388053576491668151/5000000000000000000000000000000000000000 : ℝ) v490 (190002201193255667704776107154484234543/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v491 : ℝ := j135.tangent*j118.value
  have h491 : Bounds (14455836070847000319125609117642865139/1250000000000000000000000000000000000000 : ℝ) v491 (115646688566776002553004872947214029391/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v492 : ℝ := j135.value*j118.tangent
  have h492 : Bounds (324757832107648572991933044694019687287/2000000000000000000000000000000000000000 : ℝ) v492 (811894580269121432479832611741891178821/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v493 : ℝ := v491+v492
  have h493 : Bounds (1739435849105018867512670096411241357547/10000000000000000000000000000000000000000 : ℝ) v493 (1739435849105018867512670096430996387033/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h491 h492) (by norm_num) (by norm_num)
  obtain ⟨j145,hj145⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j118=z := ⟨_,rfl⟩
  have j145_value : Bounds (95001100596627833852388053576491668151/5000000000000000000000000000000000000000 : ℝ) j145.value (190002201193255667704776107154484234543/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h490
  have j145_tangent : Bounds (1739435849105018867512670096411241357547/10000000000000000000000000000000000000000 : ℝ) j145.tangent (1739435849105018867512670096430996387033/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h493
  let v494 : ℝ := j139.value*j121.value
  have h494 : Bounds (6032569887885867449626641402127756575467/5000000000000000000000000000000000000000 : ℝ) v494 (12065139775771734899253282804268677597667/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v495 : ℝ := j139.tangent*j121.value
  have h495 : Bounds (3671782361995138081057904715959739014861/5000000000000000000000000000000000000000 : ℝ) v495 (3671782361995138081057904715995594163597/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v496 : ℝ := j139.value*j121.tangent
  have h496 : Bounds (2217379975580902685842448135625427225089/2500000000000000000000000000000000000000 : ℝ) v496 (8869519902323610743369792542565806384901/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v497 : ℝ := v495+v496
  have h497 : Bounds (8106542313156943452742800987210593465039/5000000000000000000000000000000000000000 : ℝ) v497 (3242616925262777381097120394911398942419/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h495 h496) (by norm_num) (by norm_num)
  obtain ⟨j146,hj146⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j121=z := ⟨_,rfl⟩
  have j146_value : Bounds (6032569887885867449626641402127756575467/5000000000000000000000000000000000000000 : ℝ) j146.value (12065139775771734899253282804268677597667/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h494
  have j146_tangent : Bounds (8106542313156943452742800987210593465039/5000000000000000000000000000000000000000 : ℝ) j146.tangent (3242616925262777381097120394911398942419/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h497
  let v498 : ℝ := j145.value+j146.value
  have h498 : Bounds (3063785494241247641739514727852124121809/2500000000000000000000000000000000000000 : ℝ) v498 (1225514197696499056695805891142316183221/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_value j146_value) (by norm_num) (by norm_num)
  let v499 : ℝ := j145.tangent+j146.tangent
  have h499 : Bounds (143620163803351246183986176566659426301/80000000000000000000000000000000000000 : ℝ) v499 (2244065059427363221624784008873498887391/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_tangent j146_tangent) (by norm_num) (by norm_num)
  obtain ⟨j147,hj147⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j145 j146=z := ⟨_,rfl⟩
  have j147_value : Bounds (3063785494241247641739514727852124121809/2500000000000000000000000000000000000000 : ℝ) j147.value (1225514197696499056695805891142316183221/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj147,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h498
  have j147_tangent : Bounds (143620163803351246183986176566659426301/80000000000000000000000000000000000000 : ℝ) j147.tangent (2244065059427363221624784008873498887391/1250000000000000000000000000000000000000 : ℝ) := by
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
  have h504 : Bounds (8167616351033034635774178769229671853/5000000000000000000000000000000000000000 : ℝ) v504 (8167616351033034635774178769252566711/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v505 : ℝ := j92.tangent*j148.value
  have h505 : Bounds (10963550377464675953775341780496816647/10000000000000000000000000000000000000000 : ℝ) v505 (10963550377464675953775341780601228943/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v506 : ℝ := j92.value*j148.tangent
  have h506 : Bounds (257279915057540591026886631230734663383/10000000000000000000000000000000000000000 : ℝ) v506 (128639957528770295513443315615727925693/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v507 : ℝ := v505+v506
  have h507 : Bounds (26824346543500526698066197301123148003/1000000000000000000000000000000000000000 : ℝ) v507 (268243465435005266980661973012057080329/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h505 h506) (by norm_num) (by norm_num)
  obtain ⟨j149,hj149⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j148=z := ⟨_,rfl⟩
  have j149_value : Bounds (8167616351033034635774178769229671853/5000000000000000000000000000000000000000 : ℝ) j149.value (8167616351033034635774178769252566711/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h504
  have j149_tangent : Bounds (26824346543500526698066197301123148003/1000000000000000000000000000000000000000 : ℝ) j149.tangent (268243465435005266980661973012057080329/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h507
  let v508 : ℝ := j147.value+j149.value
  have h508 : Bounds (6135738604833528318114803634473477915471/5000000000000000000000000000000000000000 : ℝ) v508 (95870915700523879970543806788763023169/78125000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_value j149_value) (by norm_num) (by norm_num)
  let v509 : ℝ := j147.tangent+j149.tangent
  have h509 : Bounds (3644152788170782207995786808768731953531/2000000000000000000000000000000000000000 : ℝ) v509 (18220763940853911039978934044000048179457/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_tangent j149_tangent) (by norm_num) (by norm_num)
  obtain ⟨j150,hj150⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j147 j149=z := ⟨_,rfl⟩
  have j150_value : Bounds (6135738604833528318114803634473477915471/5000000000000000000000000000000000000000 : ℝ) j150.value (95870915700523879970543806788763023169/78125000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h508
  have j150_tangent : Bounds (3644152788170782207995786808768731953531/2000000000000000000000000000000000000000 : ℝ) j150.tangent (18220763940853911039978934044000048179457/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h509
  have hm02 : jetIter c d 0 2=!![j115,j126;j144,j150] := by
    rw [jetIter,hm01]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj79,← hj80,← hj81,← hj82,← hj83,← hj84,← hj85,← hj86,← hj87,← hj88,← hj89,← hj90,← hj91,← hj92,← hj93,← hj94,← hj95,← hj96,← hj97,← hj98,← hj99,← hj100,← hj101,← hj102,← hj103,← hj104,← hj105,← hj106,← hj107,← hj108,← hj109,← hj110,← hj111,← hj112,← hj113,← hj114,← hj115,← hj116,← hj117,← hj118,← hj119,← hj120,← hj121,← hj122,← hj123,← hj124,← hj125,← hj126,← hj127,← hj128,← hj129,← hj130,← hj131,← hj132,← hj133,← hj134,← hj135,← hj136,← hj137,← hj138,← hj139,← hj140,← hj141,← hj142,← hj143,← hj144,← hj145,← hj146,← hj147,← hj148,← hj149,← hj150]
    all_goals rfl
  let v510 : ℝ := -c
  have h510 : Bounds (-39810178453389828830806414063/125000000000000000000000000000 : ℝ) v510 (-318481427627118630646451312501/1000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hc) (by norm_num) (by norm_num)
  let v511 : ℝ := (1 : ℝ)+v510
  have h511 : Bounds (85189821546610171169193585937/125000000000000000000000000000 : ℝ) v511 (681518572372881369353548687499/1000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (1 : ℝ)) h510) (by norm_num) (by norm_num)
  obtain ⟨j151,hj151⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((1 : ℝ)+(-c))=z := ⟨_,rfl⟩
  have j151_value : Bounds (85189821546610171169193585937/125000000000000000000000000000 : ℝ) j151.value (681518572372881369353548687499/1000000000000000000000000000000 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h511
  have j151_tangent : Bounds (0 : ℝ) j151.tangent (0 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j152,hj152⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/16 : ℝ)=z := ⟨_,rfl⟩
  have j152_value : Bounds (-1/16 : ℝ) j152.value (-1/16 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/16 : ℝ))
  have j152_tangent : Bounds (0 : ℝ) j152.tangent (0 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j153,hj153⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant c=z := ⟨_,rfl⟩
  have j153_value : Bounds (318481427627118630646451312501/1000000000000000000000000000000 : ℝ) j153.value (39810178453389828830806414063/125000000000000000000000000000 : ℝ) := by
    convert hc using 1 <;> norm_num [← hj153,LReturnJets.constant]
  have j153_tangent : Bounds (0 : ℝ) j153.tangent (0 : ℝ) := by
    simpa only [← hj153,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v512 : ℝ := j115.value*j153.value
  have h512 : Bounds (134207716972445318316609173398817372079/625000000000000000000000000000000000000 : ℝ) v512 (53683086788978127326643669360688418041/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v513 : ℝ := j115.tangent*j153.value
  have h513 : Bounds (2927379610319921447727491593722563133613/10000000000000000000000000000000000000000 : ℝ) v513 (2927379610319921447727491593823137833261/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v514 : ℝ := j115.value*j153.tangent
  have h514 : Bounds (0 : ℝ) v514 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v515 : ℝ := v513+v514
  have h515 : Bounds (2927379610319921447727491593722563133613/10000000000000000000000000000000000000000 : ℝ) v515 (2927379610319921447727491593823137833261/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h513 h514) (by norm_num) (by norm_num)
  obtain ⟨j154,hj154⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j115 j153=z := ⟨_,rfl⟩
  have j154_value : Bounds (134207716972445318316609173398817372079/625000000000000000000000000000000000000 : ℝ) j154.value (53683086788978127326643669360688418041/250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h512
  have j154_tangent : Bounds (2927379610319921447727491593722563133613/10000000000000000000000000000000000000000 : ℝ) j154.tangent (2927379610319921447727491593823137833261/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h515
  obtain ⟨j155,hj155⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant d=z := ⟨_,rfl⟩
  have j155_value : Bounds (-205046423935149745096270174003/200000000000000000000000000000 : ℝ) j155.value (-256308029918937181370337717503/250000000000000000000000000000 : ℝ) := by
    convert hd using 1 <;> norm_num [← hj155,LReturnJets.constant]
  have j155_tangent : Bounds (0 : ℝ) j155.tangent (0 : ℝ) := by
    simpa only [← hj155,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v516 : ℝ := j126.value*j155.value
  have h516 : Bounds (-871162379226217588216250441506677791573/1000000000000000000000000000000000000000 : ℝ) v516 (-435581189613108794108125220748805451279/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v517 : ℝ := j126.tangent*j155.value
  have h517 : Bounds (-13711466095701087111389372826725885452713/10000000000000000000000000000000000000000 : ℝ) v517 (-13711466095701087111389372826422600444233/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v518 : ℝ := j126.value*j155.tangent
  have h518 : Bounds (0 : ℝ) v518 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j126_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v519 : ℝ := v517+v518
  have h519 : Bounds (-13711466095701087111389372826725885452713/10000000000000000000000000000000000000000 : ℝ) v519 (-13711466095701087111389372826422600444233/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h517 h518) (by norm_num) (by norm_num)
  obtain ⟨j156,hj156⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j126 j155=z := ⟨_,rfl⟩
  have j156_value : Bounds (-871162379226217588216250441506677791573/1000000000000000000000000000000000000000 : ℝ) j156.value (-435581189613108794108125220748805451279/500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h516
  have j156_tangent : Bounds (-13711466095701087111389372826725885452713/10000000000000000000000000000000000000000 : ℝ) j156.tangent (-13711466095701087111389372826422600444233/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h519
  let v520 : ℝ := j154.value+j156.value
  have h520 : Bounds (-3282150160351525394548378820342849981233/5000000000000000000000000000000000000000 : ℝ) v520 (-328215016035152539454837882027428615197/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_value j156_value) (by norm_num) (by norm_num)
  let v521 : ℝ := j154.tangent+j156.tangent
  have h521 : Bounds (-107840864853811656636618812330033223191/100000000000000000000000000000000000000 : ℝ) v521 (-2696021621345291415915470308149865652743/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_tangent j156_tangent) (by norm_num) (by norm_num)
  obtain ⟨j157,hj157⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j154 j156=z := ⟨_,rfl⟩
  have j157_value : Bounds (-3282150160351525394548378820342849981233/5000000000000000000000000000000000000000 : ℝ) j157.value (-328215016035152539454837882027428615197/500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h520
  have j157_tangent : Bounds (-107840864853811656636618812330033223191/100000000000000000000000000000000000000 : ℝ) j157.tangent (-2696021621345291415915470308149865652743/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h521
  let v522 : ℝ := j152.value*j157.value
  have h522 : Bounds (102567192510985168579636838133571442249/2500000000000000000000000000000000000000 : ℝ) v522 (82053754008788134863709470508571249531/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v523 : ℝ := j152.tangent*j157.value
  have h523 : Bounds (0 : ℝ) v523 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v524 : ℝ := j152.value*j157.tangent
  have h524 : Bounds (134801081067264570795773515407493282637/2000000000000000000000000000000000000000 : ℝ) v524 (42125337833520178373679223566419227809/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v525 : ℝ := v523+v524
  have h525 : Bounds (134801081067264570795773515407493282637/2000000000000000000000000000000000000000 : ℝ) v525 (42125337833520178373679223566419227809/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h523 h524) (by norm_num) (by norm_num)
  obtain ⟨j158,hj158⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j157=z := ⟨_,rfl⟩
  have j158_value : Bounds (102567192510985168579636838133571442249/2500000000000000000000000000000000000000 : ℝ) j158.value (82053754008788134863709470508571249531/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h522
  have j158_tangent : Bounds (134801081067264570795773515407493282637/2000000000000000000000000000000000000000 : ℝ) j158.tangent (42125337833520178373679223566419227809/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h525
  let v526 : ℝ := j151.value*j158.value
  have h526 : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) v526 (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v527 : ℝ := j151.tangent*j158.value
  have h527 : Bounds (0 : ℝ) v527 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v528 : ℝ := j151.value*j158.tangent
  have h528 : Bounds (229673600808207994834072023459583879543/5000000000000000000000000000000000000000 : ℝ) v528 (28709200101025999354259002933649508971/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v529 : ℝ := v527+v528
  have h529 : Bounds (229673600808207994834072023459583879543/5000000000000000000000000000000000000000 : ℝ) v529 (28709200101025999354259002933649508971/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h527 h528) (by norm_num) (by norm_num)
  obtain ⟨j159,hj159⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j158=z := ⟨_,rfl⟩
  have j159_value : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) j159.value (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h526
  have j159_tangent : Bounds (229673600808207994834072023459583879543/5000000000000000000000000000000000000000 : ℝ) j159.tangent (28709200101025999354259002933649508971/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h529
  let v530 : ℝ := -d
  have h530 : Bounds (256308029918937181370337717503/250000000000000000000000000000 : ℝ) v530 (205046423935149745096270174003/200000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hd) (by norm_num) (by norm_num)
  let v531 : ℝ := (0 : ℝ)+v530
  have h531 : Bounds (256308029918937181370337717503/250000000000000000000000000000 : ℝ) v531 (205046423935149745096270174003/200000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (0 : ℝ)) h530) (by norm_num) (by norm_num)
  obtain ⟨j160,hj160⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((0 : ℝ)+(-d))=z := ⟨_,rfl⟩
  have j160_value : Bounds (256308029918937181370337717503/250000000000000000000000000000 : ℝ) j160.value (205046423935149745096270174003/200000000000000000000000000000 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h531
  have j160_tangent : Bounds (0 : ℝ) j160.tangent (0 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v532 : ℝ := j144.value*j153.value
  have h532 : Bounds (676551760587524803402560870474093799091/2500000000000000000000000000000000000000 : ℝ) v532 (338275880293762401701280435242764215523/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v533 : ℝ := j144.tangent*j153.value
  have h533 : Bounds (851874851209465454896823585341620325879/2000000000000000000000000000000000000000 : ℝ) v533 (4259374256047327274484117926806341993589/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v534 : ℝ := j144.value*j153.tangent
  have h534 : Bounds (0 : ℝ) v534 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v535 : ℝ := v533+v534
  have h535 : Bounds (851874851209465454896823585341620325879/2000000000000000000000000000000000000000 : ℝ) v535 (4259374256047327274484117926806341993589/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h533 h534) (by norm_num) (by norm_num)
  obtain ⟨j161,hj161⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j144 j153=z := ⟨_,rfl⟩
  have j161_value : Bounds (676551760587524803402560870474093799091/2500000000000000000000000000000000000000 : ℝ) j161.value (338275880293762401701280435242764215523/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h532
  have j161_tangent : Bounds (851874851209465454896823585341620325879/2000000000000000000000000000000000000000 : ℝ) j161.tangent (4259374256047327274484117926806341993589/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h535
  let v536 : ℝ := j150.value*j155.value
  have h536 : Bounds (-12581112591219598843860649858572800952533/10000000000000000000000000000000000000000 : ℝ) v536 (-6290556295609799421930324929260452096551/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v537 : ℝ := j150.tangent*j155.value
  have h537 : Bounds (-18680512437193103895283682637088567419329/10000000000000000000000000000000000000000 : ℝ) v537 (-18680512437193103895283682636873570704581/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v538 : ℝ := j150.value*j155.tangent
  have h538 : Bounds (0 : ℝ) v538 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j150_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v539 : ℝ := v537+v538
  have h539 : Bounds (-18680512437193103895283682637088567419329/10000000000000000000000000000000000000000 : ℝ) v539 (-18680512437193103895283682636873570704581/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h537 h538) (by norm_num) (by norm_num)
  obtain ⟨j162,hj162⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j150 j155=z := ⟨_,rfl⟩
  have j162_value : Bounds (-12581112591219598843860649858572800952533/10000000000000000000000000000000000000000 : ℝ) j162.value (-6290556295609799421930324929260452096551/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h536
  have j162_tangent : Bounds (-18680512437193103895283682637088567419329/10000000000000000000000000000000000000000 : ℝ) j162.tangent (-18680512437193103895283682636873570704581/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h539
  let v540 : ℝ := j161.value+j162.value
  have h540 : Bounds (-9874905548869499630250406376676425756169/10000000000000000000000000000000000000000 : ℝ) v540 (-4937452774434749815125203188289395234459/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_value j162_value) (by norm_num) (by norm_num)
  let v541 : ℝ := j161.tangent+j162.tangent
  have h541 : Bounds (-7210569090572888310399782355190232894967/5000000000000000000000000000000000000000 : ℝ) v541 (-901321136321611038799972794379201794437/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_tangent j162_tangent) (by norm_num) (by norm_num)
  obtain ⟨j163,hj163⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j161 j162=z := ⟨_,rfl⟩
  have j163_value : Bounds (-9874905548869499630250406376676425756169/10000000000000000000000000000000000000000 : ℝ) j163.value (-4937452774434749815125203188289395234459/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h540
  have j163_tangent : Bounds (-7210569090572888310399782355190232894967/5000000000000000000000000000000000000000 : ℝ) j163.tangent (-901321136321611038799972794379201794437/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h541
  let v542 : ℝ := j152.value*j163.value
  have h542 : Bounds (617181596804343726890650398536174404307/10000000000000000000000000000000000000000 : ℝ) v542 (617181596804343726890650398542276609761/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v543 : ℝ := j152.tangent*j163.value
  have h543 : Bounds (0 : ℝ) v543 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v544 : ℝ := j152.value*j163.tangent
  have h544 : Bounds (901321136321611038799972794379201794437/10000000000000000000000000000000000000000 : ℝ) v544 (901321136321611038799972794398779111871/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v545 : ℝ := v543+v544
  have h545 : Bounds (901321136321611038799972794379201794437/10000000000000000000000000000000000000000 : ℝ) v545 (901321136321611038799972794398779111871/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h543 h544) (by norm_num) (by norm_num)
  obtain ⟨j164,hj164⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j163=z := ⟨_,rfl⟩
  have j164_value : Bounds (617181596804343726890650398536174404307/10000000000000000000000000000000000000000 : ℝ) j164.value (617181596804343726890650398542276609761/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h542
  have j164_tangent : Bounds (901321136321611038799972794379201794437/10000000000000000000000000000000000000000 : ℝ) j164.tangent (901321136321611038799972794398779111871/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h545
  let v546 : ℝ := j160.value*j164.value
  have h546 : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) v546 (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v547 : ℝ := j160.tangent*j164.value
  have h547 : Bounds (0 : ℝ) v547 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v548 : ℝ := j160.value*j164.tangent
  have h548 : Bounds (924063379099559759921418887667359418039/10000000000000000000000000000000000000000 : ℝ) v548 (924063379099559759921418887690134676099/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v549 : ℝ := v547+v548
  have h549 : Bounds (924063379099559759921418887667359418039/10000000000000000000000000000000000000000 : ℝ) v549 (924063379099559759921418887690134676099/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h547 h548) (by norm_num) (by norm_num)
  obtain ⟨j165,hj165⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j164=z := ⟨_,rfl⟩
  have j165_value : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) j165.value (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h546
  have j165_tangent : Bounds (924063379099559759921418887667359418039/10000000000000000000000000000000000000000 : ℝ) j165.tangent (924063379099559759921418887690134676099/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h549
  let v550 : ℝ := j159.value+j165.value
  have h550 : Bounds (36494407326644201253872530985702864827/400000000000000000000000000000000000000 : ℝ) v550 (91236018316610503134681327465775108919/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_value j165_value) (by norm_num) (by norm_num)
  let v551 : ℝ := j159.tangent+j165.tangent
  have h551 : Bounds (11067284645727805996716503476692217417/80000000000000000000000000000000000000 : ℝ) v551 (276682116143195149917912586925705363927/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_tangent j165_tangent) (by norm_num) (by norm_num)
  obtain ⟨j166,hj166⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j159 j165=z := ⟨_,rfl⟩
  have j166_value : Bounds (36494407326644201253872530985702864827/400000000000000000000000000000000000000 : ℝ) j166.value (91236018316610503134681327465775108919/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h550
  have j166_tangent : Bounds (11067284645727805996716503476692217417/80000000000000000000000000000000000000 : ℝ) j166.tangent (276682116143195149917912586925705363927/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h551
  let v552 : ℝ := j166.value⁻¹
  have h552 : Bounds (54802917666231560702768831396561850923989/5000000000000000000000000000000000000000 : ℝ) v552 (109605835332463121405537662794947278059641/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j166_value (by norm_num)) (by norm_num) (by norm_num)
  let v553 : ℝ := -j166.tangent
  have h553 : Bounds (-276682116143195149917912586925705363927/2000000000000000000000000000000000000000 : ℝ) v553 (-11067284645727805996716503476692217417/80000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j166_tangent) (by norm_num) (by norm_num)
  let v554 : ℝ := j166.value*j166.value
  have h554 : Bounds (16648022076537774452423789457563552549/2000000000000000000000000000000000000000 : ℝ) v554 (83240110382688872262118947290587591281/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j166_value j166_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v555 : ℝ := v554⁻¹
  have h555 : Bounds (150167989236587764590654817543634830918689/1250000000000000000000000000000000000000 : ℝ) v555 (120134391389270211672523854038905356615911/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h554 (by norm_num)) (by norm_num) (by norm_num)
  let v556 : ℝ := v553*v555
  have h556 : Bounds (-33239037631158124046605533936538276027627/2000000000000000000000000000000000000000 : ℝ) v556 (-83097594077895310116513834836057803041091/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn h553 h555 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j167,hj167⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j166=z := ⟨_,rfl⟩
  have j167_value : Bounds (54802917666231560702768831396561850923989/5000000000000000000000000000000000000000 : ℝ) j167.value (109605835332463121405537662794947278059641/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h552
  have j167_tangent : Bounds (-33239037631158124046605533936538276027627/2000000000000000000000000000000000000000 : ℝ) j167.tangent (-83097594077895310116513834836057803041091/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h556
  let v557 : ℝ := j158.value*j151.value
  have h557 : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) v557 (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v558 : ℝ := j158.tangent*j151.value
  have h558 : Bounds (229673600808207994834072023459583879543/5000000000000000000000000000000000000000 : ℝ) v558 (28709200101025999354259002933649508971/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v559 : ℝ := j158.value*j151.tangent
  have h559 : Bounds (0 : ℝ) v559 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v560 : ℝ := v558+v559
  have h560 : Bounds (229673600808207994834072023459583879543/5000000000000000000000000000000000000000 : ℝ) v560 (28709200101025999354259002933649508971/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h558 h559) (by norm_num) (by norm_num)
  obtain ⟨j168,hj168⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j151=z := ⟨_,rfl⟩
  have j168_value : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) j168.value (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h557
  have j168_tangent : Bounds (229673600808207994834072023459583879543/5000000000000000000000000000000000000000 : ℝ) j168.tangent (28709200101025999354259002933649508971/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h560
  let v561 : ℝ := j167.value*j168.value
  have h561 : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) v561 (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v562 : ℝ := j167.tangent*j168.value
  have h562 : Bounds (-2323456814421326006125055724868835537551/5000000000000000000000000000000000000000 : ℝ) v562 (-580864203605331501531263931165554660711/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v563 : ℝ := j167.value*j168.tangent
  have h563 : Bounds (5034713374079662871322079647631259810497/10000000000000000000000000000000000000000 : ℝ) v563 (5034713374079662871322079647925735745113/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v564 : ℝ := v562+v563
  have h564 : Bounds (77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) v564 (15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h562 h563) (by norm_num) (by norm_num)
  obtain ⟨j169,hj169⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j168=z := ⟨_,rfl⟩
  have j169_value : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) j169.value (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h561
  have j169_tangent : Bounds (77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) j169.tangent (15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h564
  let v565 : ℝ := -j169.value
  have h565 : Bounds (-3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) v565 (-47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_value) (by norm_num) (by norm_num)
  let v566 : ℝ := j0.value+v565
  have h566 : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) v566 (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h565) (by norm_num) (by norm_num)
  let v567 : ℝ := -j169.tangent
  have h567 : Bounds (-15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) v567 (-77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_tangent) (by norm_num) (by norm_num)
  let v568 : ℝ := j0.tangent+v567
  have h568 : Bounds (-15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) v568 (-77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h567) (by norm_num) (by norm_num)
  obtain ⟨j170,hj170⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j169=z := ⟨_,rfl⟩
  have j170_value : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) j170.value (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h566
  have j170_tangent : Bounds (-15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) j170.tangent (-77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h568
  let v569 : ℝ := j170.value*j115.value
  have h569 : Bounds (4676082961961197156336293331224428345527/10000000000000000000000000000000000000000 : ℝ) v569 (935216592392239431267258666273637988411/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v570 : ℝ := j170.tangent*j115.value
  have h570 : Bounds (-65367351356752672530283821228561868039/2500000000000000000000000000000000000000 : ℝ) v570 (-261469405427010690121135284433888435449/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v571 : ℝ := j170.value*j115.tangent
  have h571 : Bounds (6374759136344999044698055869974763242157/10000000000000000000000000000000000000000 : ℝ) v571 (6374759136344999044698055870251841640249/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v572 : ℝ := v570+v571
  have h572 : Bounds (6113289730917988354576920585060515770001/10000000000000000000000000000000000000000 : ℝ) v572 (3820806081823742721610575366136220753/6250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h570 h571) (by norm_num) (by norm_num)
  obtain ⟨j171,hj171⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j115=z := ⟨_,rfl⟩
  have j171_value : Bounds (4676082961961197156336293331224428345527/10000000000000000000000000000000000000000 : ℝ) j171.value (935216592392239431267258666273637988411/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h569
  have j171_tangent : Bounds (6113289730917988354576920585060515770001/10000000000000000000000000000000000000000 : ℝ) j171.tangent (3820806081823742721610575366136220753/6250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h572
  let v573 : ℝ := j158.value*j160.value
  have h573 : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) v573 (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v574 : ℝ := j158.tangent*j160.value
  have h574 : Bounds (138202398077174096175288688048505617707/2000000000000000000000000000000000000000 : ℝ) v574 (172752997596467620219110860067607056573/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v575 : ℝ := j158.value*j160.tangent
  have h575 : Bounds (0 : ℝ) v575 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v576 : ℝ := v574+v575
  have h576 : Bounds (138202398077174096175288688048505617707/2000000000000000000000000000000000000000 : ℝ) v576 (172752997596467620219110860067607056573/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h574 h575) (by norm_num) (by norm_num)
  obtain ⟨j172,hj172⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j160=z := ⟨_,rfl⟩
  have j172_value : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) j172.value (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h573
  have j172_tangent : Bounds (138202398077174096175288688048505617707/2000000000000000000000000000000000000000 : ℝ) j172.tangent (172752997596467620219110860067607056573/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h576
  let v577 : ℝ := j167.value*j172.value
  have h577 : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) v577 (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v578 : ℝ := j167.tangent*j172.value
  have h578 : Bounds (-6990513982708963030069104930969754961137/10000000000000000000000000000000000000000 : ℝ) v578 (-6990513982708963030069104930358429357307/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v579 : ℝ := j167.value*j172.tangent
  have h579 : Bounds (7573894643099130951065399701511847566347/10000000000000000000000000000000000000000 : ℝ) v579 (3786947321549565475532699850971830329793/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v580 : ℝ := v578+v579
  have h580 : Bounds (58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) v580 (583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h578 h579) (by norm_num) (by norm_num)
  obtain ⟨j173,hj173⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j172=z := ⟨_,rfl⟩
  have j173_value : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) j173.value (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h577
  have j173_tangent : Bounds (58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) j173.tangent (583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h580
  let v581 : ℝ := -j173.value
  have h581 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v581 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_value) (by norm_num) (by norm_num)
  let v582 : ℝ := j6.value+v581
  have h582 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v582 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h581) (by norm_num) (by norm_num)
  let v583 : ℝ := -j173.tangent
  have h583 : Bounds (-583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) v583 (-58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_tangent) (by norm_num) (by norm_num)
  let v584 : ℝ := j6.tangent+v583
  have h584 : Bounds (-583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) v584 (-58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h583) (by norm_num) (by norm_num)
  obtain ⟨j174,hj174⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j173=z := ⟨_,rfl⟩
  have j174_value : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) j174.value (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h582
  have j174_tangent : Bounds (-583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) j174.tangent (-58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h584
  let v585 : ℝ := j174.value*j144.value
  have h585 : Bounds (-783486005698744571990616749549511801631/2000000000000000000000000000000000000000 : ℝ) v585 (-1958715014246861429976541873779887909077/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v586 : ℝ := j174.tangent*j144.value
  have h586 : Bounds (-123927858468966955624107996631399133073/2500000000000000000000000000000000000000 : ℝ) v586 (-495711433875867822496431985635509804527/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v587 : ℝ := j174.value*j144.tangent
  have h587 : Bounds (-6165751678313120759228385784941082033829/10000000000000000000000000000000000000000 : ℝ) v587 (-6165751678313120759228385784607524320351/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v588 : ℝ := v586+v587
  have h588 : Bounds (-6661463112188988581724817771466678566121/10000000000000000000000000000000000000000 : ℝ) v588 (-3330731556094494290862408885121517062439/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h586 h587) (by norm_num) (by norm_num)
  obtain ⟨j175,hj175⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j144=z := ⟨_,rfl⟩
  have j175_value : Bounds (-783486005698744571990616749549511801631/2000000000000000000000000000000000000000 : ℝ) j175.value (-1958715014246861429976541873779887909077/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h585
  have j175_tangent : Bounds (-6661463112188988581724817771466678566121/10000000000000000000000000000000000000000 : ℝ) j175.tangent (-3330731556094494290862408885121517062439/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h588
  let v589 : ℝ := j171.value+j175.value
  have h589 : Bounds (189663233366868574095802395869217334343/2500000000000000000000000000000000000000 : ℝ) v589 (758652933467474296383209583808414123901/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_value j175_value) (by norm_num) (by norm_num)
  let v590 : ℝ := j171.tangent+j175.tangent
  have h590 : Bounds (-13704334531775005678697429660154069903/250000000000000000000000000000000000000 : ℝ) v590 (-274086690635500113573948592212540460039/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_tangent j175_tangent) (by norm_num) (by norm_num)
  obtain ⟨j176,hj176⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j171 j175=z := ⟨_,rfl⟩
  have j176_value : Bounds (189663233366868574095802395869217334343/2500000000000000000000000000000000000000 : ℝ) j176.value (758652933467474296383209583808414123901/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h589
  have j176_tangent : Bounds (-13704334531775005678697429660154069903/250000000000000000000000000000000000000 : ℝ) j176.tangent (-274086690635500113573948592212540460039/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h590
  let v591 : ℝ := j167.value*j159.value
  have h591 : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) v591 (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v592 : ℝ := j167.tangent*j159.value
  have h592 : Bounds (-2323456814421326006125055724868835537551/5000000000000000000000000000000000000000 : ℝ) v592 (-580864203605331501531263931165554660711/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v593 : ℝ := j167.value*j159.tangent
  have h593 : Bounds (5034713374079662871322079647631259810497/10000000000000000000000000000000000000000 : ℝ) v593 (5034713374079662871322079647925735745113/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v594 : ℝ := v592+v593
  have h594 : Bounds (77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) v594 (15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h592 h593) (by norm_num) (by norm_num)
  obtain ⟨j177,hj177⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j159=z := ⟨_,rfl⟩
  have j177_value : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) j177.value (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h591
  have j177_tangent : Bounds (77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) j177.tangent (15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h594
  let v595 : ℝ := -j177.value
  have h595 : Bounds (-3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) v595 (-47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_value) (by norm_num) (by norm_num)
  let v596 : ℝ := j0.value+v595
  have h596 : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) v596 (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h595) (by norm_num) (by norm_num)
  let v597 : ℝ := -j177.tangent
  have h597 : Bounds (-15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) v597 (-77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_tangent) (by norm_num) (by norm_num)
  let v598 : ℝ := j0.tangent+v597
  have h598 : Bounds (-15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) v598 (-77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h597) (by norm_num) (by norm_num)
  obtain ⟨j178,hj178⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j177=z := ⟨_,rfl⟩
  have j178_value : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) j178.value (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h596
  have j178_tangent : Bounds (-15511989809480434362878727944051938377/400000000000000000000000000000000000000 : ℝ) j178.tangent (-77559949047402171814393639578717747079/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h598
  let v599 : ℝ := j176.value*j178.value
  have h599 : Bounds (526152925226987058359946299640763692533/10000000000000000000000000000000000000000 : ℝ) v599 (263076462613493529179973149940225222461/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v600 : ℝ := j176.tangent*j178.value
  have h600 : Bounds (-190088916396229028742390890602507596447/5000000000000000000000000000000000000000 : ℝ) v600 (-380177832792458057484781779824020146197/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j176_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v601 : ℝ := j176.value*j178.tangent
  have h601 : Bounds (-735513535804993703575144788534772699/250000000000000000000000000000000000000 : ℝ) v601 (-14710270716099874071502895737421501883/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v602 : ℝ := v600+v601
  have h602 : Bounds (-204799187112328902813893786373203050427/5000000000000000000000000000000000000000 : ℝ) v602 (-409598374224657805627787571298863149963/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h600 h601) (by norm_num) (by norm_num)
  obtain ⟨j179,hj179⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j178=z := ⟨_,rfl⟩
  have j179_value : Bounds (526152925226987058359946299640763692533/10000000000000000000000000000000000000000 : ℝ) j179.value (263076462613493529179973149940225222461/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h599
  have j179_tangent : Bounds (-204799187112328902813893786373203050427/5000000000000000000000000000000000000000 : ℝ) j179.tangent (-409598374224657805627787571298863149963/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h602
  let v603 : ℝ := j170.value*j126.value
  have h603 : Bounds (1473281600312944653162412978782232909359/2500000000000000000000000000000000000000 : ℝ) v603 (147328160031294465316241297882055252043/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v604 : ℝ := j170.tangent*j126.value
  have h604 : Bounds (-82380502483389652681596104729739125649/2500000000000000000000000000000000000000 : ℝ) v604 (-65904401986711722145276883663026910421/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v605 : ℝ := j170.value*j126.tangent
  have h605 : Bounds (4637677474101658762583898817268674263311/5000000000000000000000000000000000000000 : ℝ) v605 (9275354948203317525167797634887223936347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v606 : ℝ := v604+v605
  have h606 : Bounds (4472916469134879457220706607809196012013/5000000000000000000000000000000000000000 : ℝ) v606 (4472916469134879457220706608286044692121/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h604 h605) (by norm_num) (by norm_num)
  obtain ⟨j180,hj180⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j126=z := ⟨_,rfl⟩
  have j180_value : Bounds (1473281600312944653162412978782232909359/2500000000000000000000000000000000000000 : ℝ) j180.value (147328160031294465316241297882055252043/250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h603
  have j180_tangent : Bounds (4472916469134879457220706607809196012013/5000000000000000000000000000000000000000 : ℝ) j180.tangent (4472916469134879457220706608286044692121/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h606
  let v607 : ℝ := j174.value*j150.value
  have h607 : Bounds (-5657455995801899525654765889147437808099/10000000000000000000000000000000000000000 : ℝ) v607 (-1414363998950474881413691472227947698813/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v608 : ℝ := j174.tangent*j150.value
  have h608 : Bounds (-2237169524543269572234442551251927833/31250000000000000000000000000000000000 : ℝ) v608 (-178973561963461565778755403779918353163/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v609 : ℝ := j174.value*j150.tangent
  have h609 : Bounds (-840022504577277421164942275398509579973/1000000000000000000000000000000000000000 : ℝ) v609 (-8400225045772774211649422753573176987999/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v610 : ℝ := v608+v609
  have h610 : Bounds (-911611929362662047476444437038571270629/1000000000000000000000000000000000000000 : ℝ) v610 (-9116119293626620474764444368692850400651/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h608 h609) (by norm_num) (by norm_num)
  obtain ⟨j181,hj181⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j150=z := ⟨_,rfl⟩
  have j181_value : Bounds (-5657455995801899525654765889147437808099/10000000000000000000000000000000000000000 : ℝ) j181.value (-1414363998950474881413691472227947698813/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h607
  have j181_tangent : Bounds (-911611929362662047476444437038571270629/1000000000000000000000000000000000000000 : ℝ) j181.tangent (-9116119293626620474764444368692850400651/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h610
  let v611 : ℝ := j180.value+j181.value
  have h611 : Bounds (235670405449879086994886025981493829337/10000000000000000000000000000000000000000 : ℝ) v611 (58917601362469771748721506592604821617/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_value j181_value) (by norm_num) (by norm_num)
  let v612 : ℝ := j180.tangent+j181.tangent
  have h612 : Bounds (-21285794419607695040378894345915085283/1250000000000000000000000000000000000000 : ℝ) v612 (-170286355356861560323031152120761016409/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_tangent j181_tangent) (by norm_num) (by norm_num)
  obtain ⟨j182,hj182⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j180 j181=z := ⟨_,rfl⟩
  have j182_value : Bounds (235670405449879086994886025981493829337/10000000000000000000000000000000000000000 : ℝ) j182.value (58917601362469771748721506592604821617/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h611
  have j182_tangent : Bounds (-21285794419607695040378894345915085283/1250000000000000000000000000000000000000 : ℝ) j182.tangent (-170286355356861560323031152120761016409/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h612
  let v613 : ℝ := j160.value*j158.value
  have h613 : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) v613 (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v614 : ℝ := j160.tangent*j158.value
  have h614 : Bounds (0 : ℝ) v614 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v615 : ℝ := j160.value*j158.tangent
  have h615 : Bounds (138202398077174096175288688048505617707/2000000000000000000000000000000000000000 : ℝ) v615 (172752997596467620219110860067607056573/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v616 : ℝ := v614+v615
  have h616 : Bounds (138202398077174096175288688048505617707/2000000000000000000000000000000000000000 : ℝ) v616 (172752997596467620219110860067607056573/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h614 h615) (by norm_num) (by norm_num)
  obtain ⟨j183,hj183⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j158=z := ⟨_,rfl⟩
  have j183_value : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) j183.value (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h613
  have j183_tangent : Bounds (138202398077174096175288688048505617707/2000000000000000000000000000000000000000 : ℝ) j183.tangent (172752997596467620219110860067607056573/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h616
  let v617 : ℝ := j167.value*j183.value
  have h617 : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) v617 (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v618 : ℝ := j167.tangent*j183.value
  have h618 : Bounds (-6990513982708963030069104930969754961137/10000000000000000000000000000000000000000 : ℝ) v618 (-6990513982708963030069104930358429357307/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v619 : ℝ := j167.value*j183.tangent
  have h619 : Bounds (7573894643099130951065399701511847566347/10000000000000000000000000000000000000000 : ℝ) v619 (3786947321549565475532699850971830329793/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v620 : ℝ := v618+v619
  have h620 : Bounds (58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) v620 (583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h618 h619) (by norm_num) (by norm_num)
  obtain ⟨j184,hj184⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j183=z := ⟨_,rfl⟩
  have j184_value : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) j184.value (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h617
  have j184_tangent : Bounds (58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) j184.tangent (583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h620
  let v621 : ℝ := -j184.value
  have h621 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v621 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_value) (by norm_num) (by norm_num)
  let v622 : ℝ := j6.value+v621
  have h622 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v622 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h621) (by norm_num) (by norm_num)
  let v623 : ℝ := -j184.tangent
  have h623 : Bounds (-583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) v623 (-58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_tangent) (by norm_num) (by norm_num)
  let v624 : ℝ := j6.tangent+v623
  have h624 : Bounds (-583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) v624 (-58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h623) (by norm_num) (by norm_num)
  obtain ⟨j185,hj185⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j184=z := ⟨_,rfl⟩
  have j185_value : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) j185.value (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h622
  have j185_tangent : Bounds (-583380660390167920996294771585231302279/10000000000000000000000000000000000000000 : ℝ) j185.tangent (-58338066039016792099629477054209260521/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h624
  let v625 : ℝ := j182.value*j185.value
  have h625 : Bounds (-108649914396219407317622471158612640989/10000000000000000000000000000000000000000 : ℝ) v625 (-108649914396219407317622470974913051739/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v626 : ℝ := j182.tangent*j185.value
  have h626 : Bounds (78506242211655256684427694339924452289/10000000000000000000000000000000000000000 : ℝ) v626 (78506242211655256684427695563230102329/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j182_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v627 : ℝ := j182.value*j185.tangent
  have h627 : Bounds (-13748555676576909082600720708013247461/10000000000000000000000000000000000000000 : ℝ) v627 (-1374855567657690908260072066074039649/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v628 : ℝ := v626+v627
  have h628 : Bounds (16189421633769586900456743407977801207/2500000000000000000000000000000000000000 : ℝ) v628 (64757686535078347601826974902489705839/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h626 h627) (by norm_num) (by norm_num)
  obtain ⟨j186,hj186⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j185=z := ⟨_,rfl⟩
  have j186_value : Bounds (-108649914396219407317622471158612640989/10000000000000000000000000000000000000000 : ℝ) j186.value (-108649914396219407317622470974913051739/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h625
  have j186_tangent : Bounds (16189421633769586900456743407977801207/2500000000000000000000000000000000000000 : ℝ) j186.tangent (64757686535078347601826974902489705839/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h628
  let v629 : ℝ := j179.value+j186.value
  have h629 : Bounds (52187876353845956380290478560268881443/1250000000000000000000000000000000000000 : ℝ) v629 (417503010830767651042323828905537393183/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_value j186_value) (by norm_num) (by norm_num)
  let v630 : ℝ := j179.tangent+j186.tangent
  have h630 : Bounds (-172420343844789729012980299557247448013/5000000000000000000000000000000000000000 : ℝ) v630 (-86210171922394864506490149099093361031/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_tangent j186_tangent) (by norm_num) (by norm_num)
  obtain ⟨j187,hj187⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j179 j186=z := ⟨_,rfl⟩
  have j187_value : Bounds (52187876353845956380290478560268881443/1250000000000000000000000000000000000000 : ℝ) j187.value (417503010830767651042323828905537393183/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h629
  have j187_tangent : Bounds (-172420343844789729012980299557247448013/5000000000000000000000000000000000000000 : ℝ) j187.tangent (-86210171922394864506490149099093361031/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h630
  let v631 : ℝ := j158.value*j158.value
  have h631 : Bounds (16832046367336787281321280388156425739/10000000000000000000000000000000000000000 : ℝ) v631 (16832046367336787281321280388859665687/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v632 : ℝ := j158.tangent*j158.value
  have h632 : Bounds (27652336865030086562962346717316042319/10000000000000000000000000000000000000000 : ℝ) v632 (221218694920240692503698773751434129/80000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v633 : ℝ := j158.value*j158.tangent
  have h633 : Bounds (27652336865030086562962346717316042319/10000000000000000000000000000000000000000 : ℝ) v633 (221218694920240692503698773751434129/80000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v634 : ℝ := v632+v633
  have h634 : Bounds (27652336865030086562962346717316042319/5000000000000000000000000000000000000000 : ℝ) v634 (221218694920240692503698773751434129/40000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h632 h633) (by norm_num) (by norm_num)
  obtain ⟨j188,hj188⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j158=z := ⟨_,rfl⟩
  have j188_value : Bounds (16832046367336787281321280388156425739/10000000000000000000000000000000000000000 : ℝ) j188.value (16832046367336787281321280388859665687/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h631
  have j188_tangent : Bounds (27652336865030086562962346717316042319/5000000000000000000000000000000000000000 : ℝ) j188.tangent (221218694920240692503698773751434129/40000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h634
  let v635 : ℝ := j167.value*j188.value
  have h635 : Bounds (184489050244669997111412834170943584049/10000000000000000000000000000000000000000 : ℝ) v635 (184489050244669997111412834181720956179/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v636 : ℝ := j167.tangent*j188.value
  have h636 : Bounds (-279740511306652936489367746296390417863/10000000000000000000000000000000000000000 : ℝ) v636 (-139870255653326468244683873133450858193/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v637 : ℝ := j167.value*j188.tangent
  have h637 : Bounds (303085748098628716616109048614599321593/5000000000000000000000000000000000000000 : ℝ) v637 (121234299239451486646443619454929524099/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v638 : ℝ := v636+v637
  have h638 : Bounds (326430984890604496742850350932808225323/10000000000000000000000000000000000000000 : ℝ) v638 (326430984890604496742850351007745904109/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h636 h637) (by norm_num) (by norm_num)
  obtain ⟨j189,hj189⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j188=z := ⟨_,rfl⟩
  have j189_value : Bounds (184489050244669997111412834170943584049/10000000000000000000000000000000000000000 : ℝ) j189.value (184489050244669997111412834181720956179/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h635
  have j189_tangent : Bounds (326430984890604496742850350932808225323/10000000000000000000000000000000000000000 : ℝ) j189.tangent (326430984890604496742850351007745904109/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h638
  let v639 : ℝ := j187.value+j189.value
  have h639 : Bounds (601992061075437648153736662653094635593/10000000000000000000000000000000000000000 : ℝ) v639 (300996030537718824076868331543629174681/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_value j189_value) (by norm_num) (by norm_num)
  let v640 : ℝ := j187.tangent+j189.tangent
  have h640 : Bounds (-18409702798974961283110248181686670703/10000000000000000000000000000000000000000 : ℝ) v640 (-3681940559794992256622049077725508003/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_tangent j189_tangent) (by norm_num) (by norm_num)
  obtain ⟨j190,hj190⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j187 j189=z := ⟨_,rfl⟩
  have j190_value : Bounds (601992061075437648153736662653094635593/10000000000000000000000000000000000000000 : ℝ) j190.value (300996030537718824076868331543629174681/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h639
  have j190_tangent : Bounds (-18409702798974961283110248181686670703/10000000000000000000000000000000000000000 : ℝ) j190.tangent (-3681940559794992256622049077725508003/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h640
  let v641 : ℝ := j151.value*j164.value
  have h641 : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) v641 (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v642 : ℝ := j151.tangent*j164.value
  have h642 : Bounds (0 : ℝ) v642 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v643 : ℝ := j151.value*j164.tangent
  have h643 : Bounds (614267094075407547441292905656318082283/10000000000000000000000000000000000000000 : ℝ) v643 (614267094075407547441292905672364351121/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v644 : ℝ := v642+v643
  have h644 : Bounds (614267094075407547441292905656318082283/10000000000000000000000000000000000000000 : ℝ) v644 (614267094075407547441292905672364351121/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h642 h643) (by norm_num) (by norm_num)
  obtain ⟨j191,hj191⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j164=z := ⟨_,rfl⟩
  have j191_value : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) j191.value (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h641
  have j191_tangent : Bounds (614267094075407547441292905656318082283/10000000000000000000000000000000000000000 : ℝ) j191.tangent (614267094075407547441292905672364351121/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h644
  let v645 : ℝ := j167.value*j191.value
  have h645 : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) v645 (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v646 : ℝ := j167.tangent*j191.value
  have h646 : Bounds (-3495256991354481515034552465465248401031/5000000000000000000000000000000000000000 : ℝ) v646 (-873814247838620378758638116298221169047/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v647 : ℝ := j167.value*j191.tangent
  have h647 : Bounds (3366362898168987633781203331769469509343/5000000000000000000000000000000000000000 : ℝ) v647 (6732725796337975267562406663826831774719/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v648 : ℝ := v646+v647
  have h648 : Bounds (-16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) v648 (-257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h646 h647) (by norm_num) (by norm_num)
  obtain ⟨j192,hj192⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j191=z := ⟨_,rfl⟩
  have j192_value : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) j192.value (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h645
  have j192_tangent : Bounds (-16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) j192.tangent (-257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h648
  let v649 : ℝ := -j192.value
  have h649 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v649 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_value) (by norm_num) (by norm_num)
  let v650 : ℝ := j6.value+v649
  have h650 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v650 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h649) (by norm_num) (by norm_num)
  let v651 : ℝ := -j192.tangent
  have h651 : Bounds (257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) v651 (16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_tangent) (by norm_num) (by norm_num)
  let v652 : ℝ := j6.tangent+v651
  have h652 : Bounds (257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) v652 (16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h651) (by norm_num) (by norm_num)
  obtain ⟨j193,hj193⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j192=z := ⟨_,rfl⟩
  have j193_value : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) j193.value (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h650
  have j193_tangent : Bounds (257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) j193.tangent (16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h652
  let v653 : ℝ := j176.value*j193.value
  have h653 : Bounds (-349757858312048446604033745818953581701/10000000000000000000000000000000000000000 : ℝ) v653 (-349757858312048446604033745655286327909/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v654 : ℝ := j176.tangent*j193.value
  have h654 : Bounds (252721553373178850830409674506251718837/10000000000000000000000000000000000000000 : ℝ) v654 (12636077668658942541520483771369777691/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j176_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v655 : ℝ := j176.value*j193.tangent
  have h655 : Bounds (4889294095090246079312381867446789087/2500000000000000000000000000000000000000 : ℝ) v655 (1222323523772561519828095471343810339/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v656 : ℝ := v654+v655
  have h656 : Bounds (54455745950707967029531840395207775037/2000000000000000000000000000000000000000 : ℝ) v656 (68069682438384958786914800742224129811/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h654 h655) (by norm_num) (by norm_num)
  obtain ⟨j194,hj194⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j193=z := ⟨_,rfl⟩
  have j194_value : Bounds (-349757858312048446604033745818953581701/10000000000000000000000000000000000000000 : ℝ) j194.value (-349757858312048446604033745655286327909/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h653
  have j194_tangent : Bounds (54455745950707967029531840395207775037/2000000000000000000000000000000000000000 : ℝ) j194.tangent (68069682438384958786914800742224129811/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h656
  let v657 : ℝ := j167.value*j165.value
  have h657 : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) v657 (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v658 : ℝ := j167.tangent*j165.value
  have h658 : Bounds (-2629018400467897490032366102459356753749/2500000000000000000000000000000000000000 : ℝ) v658 (-10516073601871589960129464409033493826331/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v659 : ℝ := j167.value*j165.tangent
  have h659 : Bounds (2532068464158644775264374052744736691073/2500000000000000000000000000000000000000 : ℝ) v659 (1012827385663457910105749621139708688237/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v660 : ℝ := v658+v659
  have h660 : Bounds (-24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) v660 (-387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h658 h659) (by norm_num) (by norm_num)
  obtain ⟨j195,hj195⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j165=z := ⟨_,rfl⟩
  have j195_value : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) j195.value (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h657
  have j195_tangent : Bounds (-24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) j195.tangent (-387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h660
  let v661 : ℝ := -j195.value
  have h661 : Bounds (-6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) v661 (-3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_value) (by norm_num) (by norm_num)
  let v662 : ℝ := j0.value+v661
  have h662 : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) v662 (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h661) (by norm_num) (by norm_num)
  let v663 : ℝ := -j195.tangent
  have h663 : Bounds (387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) v663 (24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_tangent) (by norm_num) (by norm_num)
  let v664 : ℝ := j0.tangent+v663
  have h664 : Bounds (387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) v664 (24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h663) (by norm_num) (by norm_num)
  obtain ⟨j196,hj196⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j195=z := ⟨_,rfl⟩
  have j196_value : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) j196.value (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h662
  have j196_tangent : Bounds (387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) j196.tangent (24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h664
  let v665 : ℝ := j182.value*j196.value
  have h665 : Bounds (9028069488688830515669321142338359161/1250000000000000000000000000000000000000 : ℝ) v665 (36112277954755322062677284631356131203/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v666 : ℝ := j182.tangent*j196.value
  have h666 : Bounds (-10437336304166616509552384684583041889/2000000000000000000000000000000000000000 : ℝ) v666 (-52186681520833082547761922608361116499/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j182_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v667 : ℝ := j182.value*j196.tangent
  have h667 : Bounds (9139292319336616547096451535094940163/10000000000000000000000000000000000000000 : ℝ) v667 (2284823079834154136774112894744527663/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v668 : ℝ := v666+v667
  have h668 : Bounds (-21523694600748233000332735943910134641/5000000000000000000000000000000000000000 : ℝ) v668 (-43047389201496466000665471029383005847/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h666 h667) (by norm_num) (by norm_num)
  obtain ⟨j197,hj197⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j196=z := ⟨_,rfl⟩
  have j197_value : Bounds (9028069488688830515669321142338359161/1250000000000000000000000000000000000000 : ℝ) j197.value (36112277954755322062677284631356131203/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h665
  have j197_tangent : Bounds (-21523694600748233000332735943910134641/5000000000000000000000000000000000000000 : ℝ) j197.tangent (-43047389201496466000665471029383005847/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h668
  let v669 : ℝ := j194.value+j197.value
  have h669 : Bounds (-277533302402537802478679176680246708413/10000000000000000000000000000000000000000 : ℝ) v669 (-277533302402537802478679176392574065503/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_value j197_value) (by norm_num) (by norm_num)
  let v670 : ℝ := j194.tangent+j197.tangent
  have h670 : Bounds (229231340552043369146993730088218605903/10000000000000000000000000000000000000000 : ℝ) v670 (229231340552043369146993731939513513397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_tangent j197_tangent) (by norm_num) (by norm_num)
  obtain ⟨j198,hj198⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j194 j197=z := ⟨_,rfl⟩
  have j198_value : Bounds (-277533302402537802478679176680246708413/10000000000000000000000000000000000000000 : ℝ) j198.value (-277533302402537802478679176392574065503/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h669
  have j198_tangent : Bounds (229231340552043369146993730088218605903/10000000000000000000000000000000000000000 : ℝ) j198.tangent (229231340552043369146993731939513513397/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h670
  let v671 : ℝ := j158.value*j164.value
  have h671 : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) v671 (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v672 : ℝ := j158.tangent*j164.value
  have h672 : Bounds (41598373232023067546261383185528446531/10000000000000000000000000000000000000000 : ℝ) v672 (41598373232023067546261383187497580851/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v673 : ℝ := j158.value*j164.tangent
  have h673 : Bounds (9244597850331858595360451148814306569/2500000000000000000000000000000000000000 : ℝ) v673 (9244597850331858595360451149208224457/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v674 : ℝ := v672+v673
  have h674 : Bounds (78576764633350501927703187780785672807/10000000000000000000000000000000000000000 : ℝ) v674 (78576764633350501927703187784330478679/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h672 h673) (by norm_num) (by norm_num)
  obtain ⟨j199,hj199⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j164=z := ⟨_,rfl⟩
  have j199_value : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) j199.value (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h671
  have j199_tangent : Bounds (78576764633350501927703187780785672807/10000000000000000000000000000000000000000 : ℝ) j199.tangent (78576764633350501927703187784330478679/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h674
  let v675 : ℝ := j167.value*j199.value
  have h675 : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) v675 (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v676 : ℝ := j167.tangent*j199.value
  have h676 : Bounds (-42082339204276349518854805807912716621/1000000000000000000000000000000000000000 : ℝ) v676 (-420823392042763495188548058039396479327/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v677 : ℝ := j167.value*j199.tangent
  have h677 : Bounds (430623596268036352570349178296493650941/5000000000000000000000000000000000000000 : ℝ) v677 (86124719253607270514069835664616951463/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v678 : ℝ := v676+v677
  have h678 : Bounds (55052975061663651244018787314232516959/1250000000000000000000000000000000000000 : ℝ) v678 (440423800493309209952150298606773035303/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h676 h677) (by norm_num) (by norm_num)
  obtain ⟨j200,hj200⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j199=z := ⟨_,rfl⟩
  have j200_value : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) j200.value (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h675
  have j200_tangent : Bounds (55052975061663651244018787314232516959/1250000000000000000000000000000000000000 : ℝ) j200.tangent (440423800493309209952150298606773035303/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h678
  let v679 : ℝ := j198.value+j200.value
  have h679 : Bounds (-37506091341/2500000000000000000000000000000000000000 : ℝ) v679 (150807438027/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_value j200_value) (by norm_num) (by norm_num)
  let v680 : ℝ := j198.tangent+j200.tangent
  have h680 : Bounds (26786205641814103163965761144083149663/400000000000000000000000000000000000000 : ℝ) v680 (6696551410453525790991440305462865487/100000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_tangent j200_tangent) (by norm_num) (by norm_num)
  obtain ⟨j201,hj201⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j198 j200=z := ⟨_,rfl⟩
  have j201_value : Bounds (-37506091341/2500000000000000000000000000000000000000 : ℝ) j201.value (150807438027/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h679
  have j201_tangent : Bounds (26786205641814103163965761144083149663/400000000000000000000000000000000000000 : ℝ) j201.tangent (6696551410453525790991440305462865487/100000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h680
  let v681 : ℝ := j164.value*j151.value
  have h681 : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) v681 (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v682 : ℝ := j164.tangent*j151.value
  have h682 : Bounds (614267094075407547441292905656318082283/10000000000000000000000000000000000000000 : ℝ) v682 (614267094075407547441292905672364351121/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v683 : ℝ := j164.value*j151.tangent
  have h683 : Bounds (0 : ℝ) v683 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v684 : ℝ := v682+v683
  have h684 : Bounds (614267094075407547441292905656318082283/10000000000000000000000000000000000000000 : ℝ) v684 (614267094075407547441292905672364351121/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h682 h683) (by norm_num) (by norm_num)
  obtain ⟨j202,hj202⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j151=z := ⟨_,rfl⟩
  have j202_value : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) j202.value (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h681
  have j202_tangent : Bounds (614267094075407547441292905656318082283/10000000000000000000000000000000000000000 : ℝ) j202.tangent (614267094075407547441292905672364351121/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h684
  let v685 : ℝ := j167.value*j202.value
  have h685 : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) v685 (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v686 : ℝ := j167.tangent*j202.value
  have h686 : Bounds (-3495256991354481515034552465465248401031/5000000000000000000000000000000000000000 : ℝ) v686 (-873814247838620378758638116298221169047/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v687 : ℝ := j167.value*j202.tangent
  have h687 : Bounds (3366362898168987633781203331769469509343/5000000000000000000000000000000000000000 : ℝ) v687 (6732725796337975267562406663826831774719/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v688 : ℝ := v686+v687
  have h688 : Bounds (-16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) v688 (-257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h686 h687) (by norm_num) (by norm_num)
  obtain ⟨j203,hj203⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j202=z := ⟨_,rfl⟩
  have j203_value : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) j203.value (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h685
  have j203_tangent : Bounds (-16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) j203.tangent (-257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h688
  let v689 : ℝ := -j203.value
  have h689 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v689 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_value) (by norm_num) (by norm_num)
  let v690 : ℝ := j6.value+v689
  have h690 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v690 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h689) (by norm_num) (by norm_num)
  let v691 : ℝ := -j203.tangent
  have h691 : Bounds (257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) v691 (16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_tangent) (by norm_num) (by norm_num)
  let v692 : ℝ := j6.tangent+v691
  have h692 : Bounds (257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) v692 (16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h691) (by norm_num) (by norm_num)
  obtain ⟨j204,hj204⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j203=z := ⟨_,rfl⟩
  have j204_value : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) j204.value (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h690
  have j204_tangent : Bounds (257788186370987762506698266558937577657/10000000000000000000000000000000000000000 : ℝ) j204.tangent (16111761648186735156668641711972361461/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h692
  let v693 : ℝ := j204.value*j115.value
  have h693 : Bounds (-3108405719419768217666238163447733073573/10000000000000000000000000000000000000000 : ℝ) v693 (-3108405719419768217666238163313628083151/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v694 : ℝ := j204.tangent*j115.value
  have h694 : Bounds (173810644912452380869167081390205389281/10000000000000000000000000000000000000000 : ℝ) v694 (173810644912452380869167081953713009271/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v695 : ℝ := j204.value*j115.tangent
  have h695 : Bounds (-4237593284920561197273562655476460812123/10000000000000000000000000000000000000000 : ℝ) v695 (-84751865698411223945471253104794672723/200000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v696 : ℝ := v694+v695
  have h696 : Bounds (-2031891320004054408202197787043127711421/5000000000000000000000000000000000000000 : ℝ) v696 (-4063782640008108816404395573286020626879/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h694 h695) (by norm_num) (by norm_num)
  obtain ⟨j205,hj205⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j115=z := ⟨_,rfl⟩
  have j205_value : Bounds (-3108405719419768217666238163447733073573/10000000000000000000000000000000000000000 : ℝ) j205.value (-3108405719419768217666238163313628083151/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h693
  have j205_tangent : Bounds (-2031891320004054408202197787043127711421/5000000000000000000000000000000000000000 : ℝ) j205.tangent (-4063782640008108816404395573286020626879/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h696
  let v697 : ℝ := j164.value*j160.value
  have h697 : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) v697 (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v698 : ℝ := j164.tangent*j160.value
  have h698 : Bounds (924063379099559759921418887667359418039/10000000000000000000000000000000000000000 : ℝ) v698 (924063379099559759921418887690134676099/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v699 : ℝ := j164.value*j160.tangent
  have h699 : Bounds (0 : ℝ) v699 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v700 : ℝ := v698+v699
  have h700 : Bounds (924063379099559759921418887667359418039/10000000000000000000000000000000000000000 : ℝ) v700 (924063379099559759921418887690134676099/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h698 h699) (by norm_num) (by norm_num)
  obtain ⟨j206,hj206⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j160=z := ⟨_,rfl⟩
  have j206_value : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) j206.value (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h697
  have j206_tangent : Bounds (924063379099559759921418887667359418039/10000000000000000000000000000000000000000 : ℝ) j206.tangent (924063379099559759921418887690134676099/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h700
  let v701 : ℝ := j167.value*j206.value
  have h701 : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) v701 (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v702 : ℝ := j167.tangent*j206.value
  have h702 : Bounds (-2629018400467897490032366102459356753749/2500000000000000000000000000000000000000 : ℝ) v702 (-10516073601871589960129464409033493826331/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v703 : ℝ := j167.value*j206.tangent
  have h703 : Bounds (2532068464158644775264374052744736691073/2500000000000000000000000000000000000000 : ℝ) v703 (1012827385663457910105749621139708688237/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v704 : ℝ := v702+v703
  have h704 : Bounds (-24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) v704 (-387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h702 h703) (by norm_num) (by norm_num)
  obtain ⟨j207,hj207⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j206=z := ⟨_,rfl⟩
  have j207_value : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) j207.value (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h701
  have j207_tangent : Bounds (-24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) j207.tangent (-387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h704
  let v705 : ℝ := -j207.value
  have h705 : Bounds (-6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) v705 (-3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_value) (by norm_num) (by norm_num)
  let v706 : ℝ := j0.value+v705
  have h706 : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) v706 (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h705) (by norm_num) (by norm_num)
  let v707 : ℝ := -j207.tangent
  have h707 : Bounds (387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) v707 (24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_tangent) (by norm_num) (by norm_num)
  let v708 : ℝ := j0.tangent+v707
  have h708 : Bounds (387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) v708 (24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h707) (by norm_num) (by norm_num)
  obtain ⟨j208,hj208⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j207=z := ⟨_,rfl⟩
  have j208_value : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) j208.value (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h706
  have j208_tangent : Bounds (387799745237010859071968197636406943961/10000000000000000000000000000000000000000 : ℝ) j208.tangent (24237484077313178691998012428655015669/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h708
  let v709 : ℝ := j208.value*j144.value
  have h709 : Bounds (2604094496409338938072053552706227758953/10000000000000000000000000000000000000000 : ℝ) v709 (651023624102334734518013388224817224351/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v710 : ℝ := j208.tangent*j144.value
  have h710 : Bounds (164761004966779305363192209048300751419/5000000000000000000000000000000000000000 : ℝ) v710 (329522009933558610726384419137489551731/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v711 : ℝ := j208.value*j144.tangent
  have h711 : Bounds (4098656490335720215634400319856782524857/10000000000000000000000000000000000000000 : ℝ) v711 (1024664122583930053908600080046469004921/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v712 : ℝ := v710+v711
  have h712 : Bounds (885635700053855765272156947590676805539/2000000000000000000000000000000000000000 : ℝ) v712 (885635700053855765272156947864673114283/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h710 h711) (by norm_num) (by norm_num)
  obtain ⟨j209,hj209⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j144=z := ⟨_,rfl⟩
  have j209_value : Bounds (2604094496409338938072053552706227758953/10000000000000000000000000000000000000000 : ℝ) j209.value (651023624102334734518013388224817224351/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h709
  have j209_tangent : Bounds (885635700053855765272156947590676805539/2000000000000000000000000000000000000000 : ℝ) j209.tangent (885635700053855765272156947864673114283/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h712
  let v713 : ℝ := j205.value+j209.value
  have h713 : Bounds (-25215561150521463979709230537075265731/500000000000000000000000000000000000000 : ℝ) v713 (-504311223010429279594184610414359185747/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_value j209_value) (by norm_num) (by norm_num)
  let v714 : ℝ := j205.tangent+j209.tangent
  have h714 : Bounds (364395860261170009956389163867128604853/10000000000000000000000000000000000000000 : ℝ) v714 (45549482532646251244548645754668118067/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_tangent j209_tangent) (by norm_num) (by norm_num)
  obtain ⟨j210,hj210⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j205 j209=z := ⟨_,rfl⟩
  have j210_value : Bounds (-25215561150521463979709230537075265731/500000000000000000000000000000000000000 : ℝ) j210.value (-504311223010429279594184610414359185747/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h713
  have j210_tangent : Bounds (364395860261170009956389163867128604853/10000000000000000000000000000000000000000 : ℝ) j210.tangent (45549482532646251244548645754668118067/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h714
  let v715 : ℝ := j210.value*j178.value
  have h715 : Bounds (-349757858312048446604033745853803888681/10000000000000000000000000000000000000000 : ℝ) v715 (-174878929156024223302016872810218010463/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v716 : ℝ := j210.tangent*j178.value
  have h716 : Bounds (50544310674635770166081934842384223277/2000000000000000000000000000000000000000 : ℝ) v716 (252721553373178850830409675721726156129/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j210_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v717 : ℝ := j210.value*j178.tangent
  have h717 : Bounds (3911435276072196863449905496291080759/2000000000000000000000000000000000000000 : ℝ) v717 (3911435276072196863449905505966543597/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v718 : ℝ := v716+v717
  have h718 : Bounds (13613936487676991757382960084668826009/500000000000000000000000000000000000000 : ℝ) v718 (136139364876769917573829601625779437057/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h716 h717) (by norm_num) (by norm_num)
  obtain ⟨j211,hj211⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j178=z := ⟨_,rfl⟩
  have j211_value : Bounds (-349757858312048446604033745853803888681/10000000000000000000000000000000000000000 : ℝ) j211.value (-174878929156024223302016872810218010463/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h715
  have j211_tangent : Bounds (13613936487676991757382960084668826009/500000000000000000000000000000000000000 : ℝ) j211.tangent (136139364876769917573829601625779437057/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h718
  let v719 : ℝ := j204.value*j126.value
  have h719 : Bounds (-391743002849372285995308374772555903911/1000000000000000000000000000000000000000 : ℝ) v719 (-3917430028493722859953083747575096940167/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v720 : ℝ := j204.tangent*j126.value
  have h720 : Bounds (219048316440171610448176757739038621411/10000000000000000000000000000000000000000 : ℝ) v720 (219048316440171610448176758448173243103/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v721 : ℝ := j204.value*j126.tangent
  have h721 : Bounds (-1233150335662624151845677156984711960309/2000000000000000000000000000000000000000 : ℝ) v721 (-6165751678313120759228385784614534530213/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v722 : ℝ := v720+v721
  have h722 : Bounds (-2973351680936474574390104513592260590067/5000000000000000000000000000000000000000 : ℝ) v722 (-594670336187294914878020902616636128711/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h720 h721) (by norm_num) (by norm_num)
  obtain ⟨j212,hj212⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j126=z := ⟨_,rfl⟩
  have j212_value : Bounds (-391743002849372285995308374772555903911/1000000000000000000000000000000000000000 : ℝ) j212.value (-3917430028493722859953083747575096940167/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h719
  have j212_tangent : Bounds (-2973351680936474574390104513592260590067/5000000000000000000000000000000000000000 : ℝ) j212.tangent (-594670336187294914878020902616636128711/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h722
  let v723 : ℝ := j208.value*j150.value
  have h723 : Bounds (3760769156101686211723610826750157536539/10000000000000000000000000000000000000000 : ℝ) v723 (11752403612817769411636283834391607857/31250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v724 : ℝ := j208.tangent*j150.value
  have h724 : Bounds (47588757355906694539756677548181879751/1000000000000000000000000000000000000000 : ℝ) v724 (118971893389766736349391694245513442041/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v725 : ℝ := j208.value*j150.tangent
  have h725 : Bounds (5584012899065829535850028458871273933261/10000000000000000000000000000000000000000 : ℝ) v725 (5584012899065829535850028459291365868411/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v726 : ℝ := v724+v725
  have h726 : Bounds (6059900472624896481247595234353092730771/10000000000000000000000000000000000000000 : ℝ) v726 (242396018904995859249903809450936785463/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h724 h725) (by norm_num) (by norm_num)
  obtain ⟨j213,hj213⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j150=z := ⟨_,rfl⟩
  have j213_value : Bounds (3760769156101686211723610826750157536539/10000000000000000000000000000000000000000 : ℝ) j213.value (11752403612817769411636283834391607857/31250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h723
  have j213_tangent : Bounds (6059900472624896481247595234353092730771/10000000000000000000000000000000000000000 : ℝ) j213.tangent (242396018904995859249903809450936785463/400000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h726
  let v727 : ℝ := j212.value+j213.value
  have h727 : Bounds (-156660872392036648229472920975401502571/10000000000000000000000000000000000000000 : ℝ) v727 (-156660872392036648229472920569782425927/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_value j213_value) (by norm_num) (by norm_num)
  let v728 : ℝ := j212.tangent+j213.tangent
  have h728 : Bounds (113197110751947332467386207168571550637/10000000000000000000000000000000000000000 : ℝ) v728 (22639422150389466493477242021411669893/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_tangent j213_tangent) (by norm_num) (by norm_num)
  obtain ⟨j214,hj214⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j212 j213=z := ⟨_,rfl⟩
  have j214_value : Bounds (-156660872392036648229472920975401502571/10000000000000000000000000000000000000000 : ℝ) j214.value (-156660872392036648229472920569782425927/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h727
  have j214_tangent : Bounds (113197110751947332467386207168571550637/10000000000000000000000000000000000000000 : ℝ) j214.tangent (22639422150389466493477242021411669893/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h728
  let v729 : ℝ := j214.value*j185.value
  have h729 : Bounds (72224555909510644125354569105748456041/10000000000000000000000000000000000000000 : ℝ) v729 (72224555909510644125354569295670679649/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v730 : ℝ := j214.tangent*j185.value
  have h730 : Bounds (-52186681520833082547761923694051458627/10000000000000000000000000000000000000000 : ℝ) v730 (-26093340760416541273880961168612433593/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j214_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v731 : ℝ := j214.value*j185.tangent
  have h731 : Bounds (9139292319336616547096451537034058253/10000000000000000000000000000000000000000 : ℝ) v731 (1827858463867323309419290315407798513/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v732 : ℝ := v730+v731
  have h732 : Bounds (-21523694600748233000332736078508700187/5000000000000000000000000000000000000000 : ℝ) v732 (-43047389201496466000665470760185874621/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h730 h731) (by norm_num) (by norm_num)
  obtain ⟨j215,hj215⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j185=z := ⟨_,rfl⟩
  have j215_value : Bounds (72224555909510644125354569105748456041/10000000000000000000000000000000000000000 : ℝ) j215.value (72224555909510644125354569295670679649/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h729
  have j215_tangent : Bounds (-21523694600748233000332736078508700187/5000000000000000000000000000000000000000 : ℝ) j215.tangent (-43047389201496466000665470760185874621/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h732
  let v733 : ℝ := j211.value+j215.value
  have h733 : Bounds (-867291570007930632745872427337673227/31250000000000000000000000000000000000 : ℝ) v733 (-277533302402537802478679176324765341277/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_value j215_value) (by norm_num) (by norm_num)
  let v734 : ℝ := j211.tangent+j215.tangent
  have h734 : Bounds (114615670276021684573496864768179559903/5000000000000000000000000000000000000000 : ℝ) v734 (229231340552043369146993732491372999493/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_tangent j215_tangent) (by norm_num) (by norm_num)
  obtain ⟨j216,hj216⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j211 j215=z := ⟨_,rfl⟩
  have j216_value : Bounds (-867291570007930632745872427337673227/31250000000000000000000000000000000000 : ℝ) j216.value (-277533302402537802478679176324765341277/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h733
  have j216_tangent : Bounds (114615670276021684573496864768179559903/5000000000000000000000000000000000000000 : ℝ) j216.tangent (229231340552043369146993732491372999493/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h734
  let v735 : ℝ := j164.value*j158.value
  have h735 : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) v735 (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v736 : ℝ := j164.tangent*j158.value
  have h736 : Bounds (9244597850331858595360451148814306569/2500000000000000000000000000000000000000 : ℝ) v736 (9244597850331858595360451149208224457/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v737 : ℝ := j164.value*j158.tangent
  have h737 : Bounds (41598373232023067546261383185528446531/10000000000000000000000000000000000000000 : ℝ) v737 (41598373232023067546261383187497580851/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v738 : ℝ := v736+v737
  have h738 : Bounds (78576764633350501927703187780785672807/10000000000000000000000000000000000000000 : ℝ) v738 (78576764633350501927703187784330478679/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h736 h737) (by norm_num) (by norm_num)
  obtain ⟨j217,hj217⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j158=z := ⟨_,rfl⟩
  have j217_value : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) j217.value (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h735
  have j217_tangent : Bounds (78576764633350501927703187780785672807/10000000000000000000000000000000000000000 : ℝ) j217.tangent (78576764633350501927703187784330478679/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h738
  let v739 : ℝ := j167.value*j217.value
  have h739 : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) v739 (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v740 : ℝ := j167.tangent*j217.value
  have h740 : Bounds (-42082339204276349518854805807912716621/1000000000000000000000000000000000000000 : ℝ) v740 (-420823392042763495188548058039396479327/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v741 : ℝ := j167.value*j217.tangent
  have h741 : Bounds (430623596268036352570349178296493650941/5000000000000000000000000000000000000000 : ℝ) v741 (86124719253607270514069835664616951463/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v742 : ℝ := v740+v741
  have h742 : Bounds (55052975061663651244018787314232516959/1250000000000000000000000000000000000000 : ℝ) v742 (440423800493309209952150298606773035303/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h740 h741) (by norm_num) (by norm_num)
  obtain ⟨j218,hj218⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j217=z := ⟨_,rfl⟩
  have j218_value : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) j218.value (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h739
  have j218_tangent : Bounds (55052975061663651244018787314232516959/1250000000000000000000000000000000000000 : ℝ) j218.tangent (440423800493309209952150298606773035303/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h742
  let v743 : ℝ := j216.value+j218.value
  have h743 : Bounds (-217833089591/10000000000000000000000000000000000000000 : ℝ) v743 (218616162253/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_value j218_value) (by norm_num) (by norm_num)
  let v744 : ℝ := j216.tangent+j218.tangent
  have h744 : Bounds (334827570522676289549572014025109627739/5000000000000000000000000000000000000000 : ℝ) v744 (167413785261338144774786007774536508699/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_tangent j218_tangent) (by norm_num) (by norm_num)
  obtain ⟨j219,hj219⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j216 j218=z := ⟨_,rfl⟩
  have j219_value : Bounds (-217833089591/10000000000000000000000000000000000000000 : ℝ) j219.value (218616162253/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h743
  have j219_tangent : Bounds (334827570522676289549572014025109627739/5000000000000000000000000000000000000000 : ℝ) j219.tangent (167413785261338144774786007774536508699/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h744
  let v745 : ℝ := j210.value*j193.value
  have h745 : Bounds (232500008240487238023263283802829985949/10000000000000000000000000000000000000000 : ℝ) v745 (232500008240487238023263283960842947381/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v746 : ℝ := j210.tangent*j193.value
  have h746 : Bounds (-83997774239271084831557702701910296457/5000000000000000000000000000000000000000 : ℝ) v746 (-33599109695708433932623080879620273521/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j210_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v747 : ℝ := j210.value*j193.tangent
  have h747 : Bounds (-13000547554639331529952735097358961043/10000000000000000000000000000000000000000 : ℝ) v747 (-13000547554639331529952735046935548893/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v748 : ℝ := v746+v747
  have h748 : Bounds (-180996096033181501193068140501179553957/10000000000000000000000000000000000000000 : ℝ) v748 (-90498048016590750596534069722518458249/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h746 h747) (by norm_num) (by norm_num)
  obtain ⟨j220,hj220⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j193=z := ⟨_,rfl⟩
  have j220_value : Bounds (232500008240487238023263283802829985949/10000000000000000000000000000000000000000 : ℝ) j220.value (232500008240487238023263283960842947381/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h745
  have j220_tangent : Bounds (-180996096033181501193068140501179553957/10000000000000000000000000000000000000000 : ℝ) j220.tangent (-90498048016590750596534069722518458249/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h748
  let v749 : ℝ := j214.value*j196.value
  have h749 : Bounds (-48010957995817240911850449769675533703/10000000000000000000000000000000000000000 : ℝ) v749 (-24005478997908620455925224821083969941/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v750 : ℝ := j214.tangent*j196.value
  have h750 : Bounds (8672717135073018945739628308719491367/2500000000000000000000000000000000000000 : ℝ) v750 (17345434270146037891479257068865612959/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j214_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v751 : ℝ := j214.value*j196.tangent
  have h751 : Bounds (-3037652320111984008132244590633357611/5000000000000000000000000000000000000000 : ℝ) v751 (-3037652320111984008132244573195855363/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v752 : ℝ := v750+v751
  have h752 : Bounds (14307781950034053883347012026805625123/5000000000000000000000000000000000000000 : ℝ) v752 (3576945487508513470836753123917439399/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h750 h751) (by norm_num) (by norm_num)
  obtain ⟨j221,hj221⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j196=z := ⟨_,rfl⟩
  have j221_value : Bounds (-48010957995817240911850449769675533703/10000000000000000000000000000000000000000 : ℝ) j221.value (-24005478997908620455925224821083969941/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h749
  have j221_tangent : Bounds (14307781950034053883347012026805625123/5000000000000000000000000000000000000000 : ℝ) j221.tangent (3576945487508513470836753123917439399/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h752
  let v753 : ℝ := j220.value+j221.value
  have h753 : Bounds (92244525122334998555706417016577226123/5000000000000000000000000000000000000000 : ℝ) v753 (184489050244669997111412834318675007499/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_value j221_value) (by norm_num) (by norm_num)
  let v754 : ℝ := j220.tangent+j221.tangent
  have h754 : Bounds (-152380532133113393426374116447568303711/10000000000000000000000000000000000000000 : ℝ) v754 (-76190266066556696713187057226848700653/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_tangent j221_tangent) (by norm_num) (by norm_num)
  obtain ⟨j222,hj222⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j220 j221=z := ⟨_,rfl⟩
  have j222_value : Bounds (92244525122334998555706417016577226123/5000000000000000000000000000000000000000 : ℝ) j222.value (184489050244669997111412834318675007499/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h753
  have j222_tangent : Bounds (-152380532133113393426374116447568303711/10000000000000000000000000000000000000000 : ℝ) j222.tangent (-76190266066556696713187057226848700653/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h754
  let v755 : ℝ := j164.value*j164.value
  have h755 : Bounds (1904565617169797534184441459407627811/500000000000000000000000000000000000000 : ℝ) v755 (19045656171697975341844414594452895001/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v756 : ℝ := j164.tangent*j164.value
  have h756 : Bounds (55627881814847747213202572053655672989/10000000000000000000000000000000000000000 : ℝ) v756 (55627881814847747213202572055413953669/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v757 : ℝ := j164.value*j164.tangent
  have h757 : Bounds (55627881814847747213202572053655672989/10000000000000000000000000000000000000000 : ℝ) v757 (55627881814847747213202572055413953669/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v758 : ℝ := v756+v757
  have h758 : Bounds (55627881814847747213202572053655672989/5000000000000000000000000000000000000000 : ℝ) v758 (55627881814847747213202572055413953669/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h756 h757) (by norm_num) (by norm_num)
  obtain ⟨j223,hj223⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j164=z := ⟨_,rfl⟩
  have j223_value : Bounds (1904565617169797534184441459407627811/500000000000000000000000000000000000000 : ℝ) j223.value (19045656171697975341844414594452895001/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h755
  have j223_tangent : Bounds (55627881814847747213202572053655672989/5000000000000000000000000000000000000000 : ℝ) j223.tangent (55627881814847747213202572055413953669/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h758
  let v759 : ℝ := j167.value*j223.value
  have h759 : Bounds (417503010830767651042323828686476261117/10000000000000000000000000000000000000000 : ℝ) v759 (104375752707691912760580957175419596003/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v760 : ℝ := j167.tangent*j223.value
  have h760 : Bounds (-633059282201167975778203131358848839693/10000000000000000000000000000000000000000 : ℝ) v760 (-158264820550291993944550782826511486349/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v761 : ℝ := j167.value*j223.tangent
  have h761 : Bounds (1219428090818384391302923657946887638479/10000000000000000000000000000000000000000 : ℝ) v761 (304857022704596097825730914501429884853/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v762 : ℝ := v760+v761
  have h762 : Bounds (293184404308608207762360263294019399393/5000000000000000000000000000000000000000 : ℝ) v762 (18324025269288012985147516459364799813/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h760 h761) (by norm_num) (by norm_num)
  obtain ⟨j224,hj224⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j223=z := ⟨_,rfl⟩
  have j224_value : Bounds (417503010830767651042323828686476261117/10000000000000000000000000000000000000000 : ℝ) j224.value (104375752707691912760580957175419596003/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h759
  have j224_tangent : Bounds (293184404308608207762360263294019399393/5000000000000000000000000000000000000000 : ℝ) j224.tangent (18324025269288012985147516459364799813/312500000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h762
  let v763 : ℝ := j222.value+j224.value
  have h763 : Bounds (601992061075437648153736662719630713363/10000000000000000000000000000000000000000 : ℝ) v763 (601992061075437648153736663020353391511/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_value j224_value) (by norm_num) (by norm_num)
  let v764 : ℝ := j222.tangent+j224.tangent
  have h764 : Bounds (17359531059364120883933856405618819803/400000000000000000000000000000000000000 : ℝ) v764 (43398827648410302209834641224597619271/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_tangent j224_tangent) (by norm_num) (by norm_num)
  obtain ⟨j225,hj225⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j222 j224=z := ⟨_,rfl⟩
  have j225_value : Bounds (601992061075437648153736662719630713363/10000000000000000000000000000000000000000 : ℝ) j225.value (601992061075437648153736663020353391511/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h763
  have j225_tangent : Bounds (17359531059364120883933856405618819803/400000000000000000000000000000000000000 : ℝ) j225.tangent (43398827648410302209834641224597619271/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h764
  have hm03 : jetIter c d 0 3=!![j190,j201;j219,j225] := by
    rw [jetIter,hm02]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj80,← hj85,← hj151,← hj152,← hj153,← hj154,← hj155,← hj156,← hj157,← hj158,← hj159,← hj160,← hj161,← hj162,← hj163,← hj164,← hj165,← hj166,← hj167,← hj168,← hj169,← hj170,← hj171,← hj172,← hj173,← hj174,← hj175,← hj176,← hj177,← hj178,← hj179,← hj180,← hj181,← hj182,← hj183,← hj184,← hj185,← hj186,← hj187,← hj188,← hj189,← hj190,← hj191,← hj192,← hj193,← hj194,← hj195,← hj196,← hj197,← hj198,← hj199,← hj200,← hj201,← hj202,← hj203,← hj204,← hj205,← hj206,← hj207,← hj208,← hj209,← hj210,← hj211,← hj212,← hj213,← hj214,← hj215,← hj216,← hj217,← hj218,← hj219,← hj220,← hj221,← hj222,← hj223,← hj224,← hj225]
    all_goals rfl
  let v765 : ℝ := j190.value⁻¹
  have h765 : Bounds (16611514746781463610085203381548610845247/1000000000000000000000000000000000000000 : ℝ) v765 (33223029493562927220170406787058059050731/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j190_value (by norm_num)) (by norm_num) (by norm_num)
  let v766 : ℝ := -j190.tangent
  have h766 : Bounds (3681940559794992256622049077725508003/2000000000000000000000000000000000000000 : ℝ) v766 (18409702798974961283110248181686670703/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j190_tangent) (by norm_num) (by norm_num)
  let v767 : ℝ := j190.value*j190.value
  have h767 : Bounds (4529930519973168144797654944532041299/1250000000000000000000000000000000000000 : ℝ) v767 (9059861039946336289595309902132238043/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j190_value j190_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v768 : ℝ := v767⁻¹
  have h768 : Bounds (1379712110912690165406980929759475127625339/5000000000000000000000000000000000000000 : ℝ) v768 (4311600346602156766896815411717512948219/15625000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h767 (by norm_num)) (by norm_num) (by norm_num)
  let v769 : ℝ := v766*v768
  have h769 : Bounds (1016003596401960174471126449353360647547/2000000000000000000000000000000000000000 : ℝ) v769 (5080017982009800872355633024817841801353/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn h766 h768 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j226,hj226⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j190=z := ⟨_,rfl⟩
  have j226_value : Bounds (16611514746781463610085203381548610845247/1000000000000000000000000000000000000000 : ℝ) j226.value (33223029493562927220170406787058059050731/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h765
  have j226_tangent : Bounds (1016003596401960174471126449353360647547/2000000000000000000000000000000000000000 : ℝ) j226.tangent (5080017982009800872355633024817841801353/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h769
  let v770 : ℝ := j201.value*j226.value
  have h770 : Bounds (-2492131957621/10000000000000000000000000000000000000000 : ℝ) v770 (250513998071/1000000000000000000000000000000000000000 : ℝ) := by
    exact mul_corners j201_value j226_value (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v771 : ℝ := j201.tangent*j226.value
  have h771 : Bounds (695249140670805959156748731860961275591/625000000000000000000000000000000000000 : ℝ) v771 (11123986250732895346507979750094366029339/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j201_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v772 : ℝ := j201.value*j226.tangent
  have h772 : Bounds (-76212647379/10000000000000000000000000000000000000000 : ℝ) v772 (766104497/100000000000000000000000000000000000000 : ℝ) := by
    exact mul_corners j201_value j226_tangent (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v773 : ℝ := v771+v772
  have h773 : Bounds (11123986250732895346507979709699167762077/10000000000000000000000000000000000000000 : ℝ) v773 (11123986250732895346507979750170976479039/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h771 h772) (by norm_num) (by norm_num)
  obtain ⟨j227,hj227⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j201 j226=z := ⟨_,rfl⟩
  have j227_value : Bounds (-2492131957621/10000000000000000000000000000000000000000 : ℝ) j227.value (250513998071/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h770
  have j227_tangent : Bounds (11123986250732895346507979709699167762077/10000000000000000000000000000000000000000 : ℝ) j227.tangent (11123986250732895346507979750170976479039/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h773
  have he00 : jacobian c d 0 0=j227.tangent := by
    simp only [jacobian,shapeJet,hm03,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj227,← hj226]
    rfl
  let v774 : ℝ := j225.value*j226.value
  have h774 : Bounds (4999999999999999999999999996946574051639/5000000000000000000000000000000000000000 : ℝ) v774 (10000000000000000000000000006100724239817/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_value j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v775 : ℝ := j225.tangent*j226.value
  have h775 : Bounds (7209202654745948431445767778234372166439/10000000000000000000000000000000000000000 : ℝ) v775 (7209202654745948431445767818409372366679/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v776 : ℝ := j225.value*j226.tangent
  have h776 : Bounds (15290652476451827792452378415289826927/500000000000000000000000000000000000000 : ℝ) v776 (1911331559556478474056547595603868953/62500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_value j226_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v777 : ℝ := v775+v776
  have h777 : Bounds (7515015704274984987294815346540168704979/10000000000000000000000000000000000000000 : ℝ) v777 (7515015704274984987294815433705991399159/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h775 h776) (by norm_num) (by norm_num)
  obtain ⟨j228,hj228⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j225 j226=z := ⟨_,rfl⟩
  have j228_value : Bounds (4999999999999999999999999996946574051639/5000000000000000000000000000000000000000 : ℝ) j228.value (10000000000000000000000000006100724239817/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h774
  have j228_tangent : Bounds (7515015704274984987294815346540168704979/10000000000000000000000000000000000000000 : ℝ) j228.tangent (7515015704274984987294815433705991399159/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h777
  have he10 : jacobian c d 1 0=j228.tangent := by
    simp only [jacobian,shapeJet,hm03,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj228,← hj226]
    rfl
  rw [he00,he10]
  exact ⟨enlarge j227_tangent (by norm_num) (by norm_num),
    enlarge j228_tangent (by norm_num) (by norm_num)⟩

theorem column_1_bounds {c d : ℝ}
    (hc : Bounds (318481427627118630646451312501/1000000000000000000000000000000 : ℝ) c (39810178453389828830806414063/125000000000000000000000000000 : ℝ))
    (hd : Bounds (-205046423935149745096270174003/200000000000000000000000000000 : ℝ) d (-256308029918937181370337717503/250000000000000000000000000000 : ℝ)) :
    Bounds (129194020546319545843/200000000000000000000 : ℝ) (jacobian c d 0 1) (25838804109263909169/40000000000000000000 : ℝ) ∧
    Bounds (98102737716635073347/200000000000000000000 : ℝ) (jacobian c d 1 1) (98102737716635073349/200000000000000000000 : ℝ) := by

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
  have h256 : Bounds (1318481427627118630646451312501/1000000000000000000000000000000 : ℝ) v256 (164810178453389828830806414063/125000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hc h255) (by norm_num) (by norm_num)
  obtain ⟨j77,hj77⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (c+(-(-1 : ℝ)))=z := ⟨_,rfl⟩
  have j77_value : Bounds (1318481427627118630646451312501/1000000000000000000000000000000 : ℝ) j77.value (164810178453389828830806414063/125000000000000000000000000000 : ℝ) := by
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
  have h271 : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) v271 (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v272 : ℝ := j77.tangent*j83.value
  have h272 : Bounds (0 : ℝ) v272 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v273 : ℝ := j77.value*j83.tangent
  have h273 : Bounds (-164810178453389828830806414063/128000000000000000000000000000000 : ℝ) v273 (-1318481427627118630646451312501/1024000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j77_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v274 : ℝ := v272+v273
  have h274 : Bounds (-164810178453389828830806414063/128000000000000000000000000000000 : ℝ) v274 (-1318481427627118630646451312501/1024000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h272 h273) (by norm_num) (by norm_num)
  obtain ⟨j84,hj84⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j83=z := ⟨_,rfl⟩
  have j84_value : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) j84.value (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h271
  have j84_tangent : Bounds (-164810178453389828830806414063/128000000000000000000000000000000 : ℝ) j84.tangent (-1318481427627118630646451312501/1024000000000000000000000000000000 : ℝ) := by
    simpa only [← hj84,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h274
  let v275 : ℝ := -(-1/8 : ℝ)
  have h275 : Bounds (1/8 : ℝ) v275 (1/8 : ℝ) := by
    exact enlarge (IntervalBounds.neg (IntervalBounds.exact (-1/8 : ℝ))) (by norm_num) (by norm_num)
  let v276 : ℝ := d+v275
  have h276 : Bounds (-180046423935149745096270174003/200000000000000000000000000000 : ℝ) v276 (-225058029918937181370337717503/250000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add hd h275) (by norm_num) (by norm_num)
  obtain ⟨j85,hj85⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (d+(-(-1/8 : ℝ)))=z := ⟨_,rfl⟩
  have j85_value : Bounds (-180046423935149745096270174003/200000000000000000000000000000 : ℝ) j85.value (-225058029918937181370337717503/250000000000000000000000000000 : ℝ) := by
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
  have h291 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v291 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v292 : ℝ := j85.tangent*j89.value
  have h292 : Bounds (0 : ℝ) v292 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v293 : ℝ := j85.value*j89.tangent
  have h293 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v293 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v294 : ℝ := v292+v293
  have h294 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v294 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h292 h293) (by norm_num) (by norm_num)
  obtain ⟨j90,hj90⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j89=z := ⟨_,rfl⟩
  have j90_value : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) j90.value (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h291
  have j90_tangent : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) j90.tangent (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    simpa only [← hj90,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h294
  let v295 : ℝ := j84.value+j90.value
  have h295 : Bounds (153043427393832086484397702767387/1024000000000000000000000000000000 : ℝ) v295 (19130428424229010810549712845977/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_value j90_value) (by norm_num) (by norm_num)
  let v296 : ℝ := j84.tangent+j90.tangent
  have h296 : Bounds (-1965274417804887279793508154093/128000000000000000000000000000000 : ℝ) v296 (-15722195342439098238348065232693/1024000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j84_tangent j90_tangent) (by norm_num) (by norm_num)
  obtain ⟨j91,hj91⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j84 j90=z := ⟨_,rfl⟩
  have j91_value : Bounds (153043427393832086484397702767387/1024000000000000000000000000000000 : ℝ) j91.value (19130428424229010810549712845977/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h295
  have j91_tangent : Bounds (-1965274417804887279793508154093/128000000000000000000000000000000 : ℝ) j91.tangent (-15722195342439098238348065232693/1024000000000000000000000000000000 : ℝ) := by
    simpa only [← hj91,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h296
  let v297 : ℝ := j91.value⁻¹
  have h297 : Bounds (8363639143457827467032759059691183977931/1250000000000000000000000000000000000000 : ℝ) v297 (33454556573831309868131036238858513246789/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j91_value (by norm_num)) (by norm_num) (by norm_num)
  let v298 : ℝ := -j91.tangent
  have h298 : Bounds (15722195342439098238348065232693/1024000000000000000000000000000000 : ℝ) v298 (1965274417804887279793508154093/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j91_tangent) (by norm_num) (by norm_num)
  let v299 : ℝ := j91.value*j91.value
  have h299 : Bounds (111686185209518210942120195720437490149/5000000000000000000000000000000000000000 : ℝ) v299 (223372370419036421884240391442127262067/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j91_value j91_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v300 : ℝ := v299⁻¹
  have h300 : Bounds (89536588444134376828468553548047042179873/2000000000000000000000000000000000000000 : ℝ) v300 (22384147111033594207117138387137251711531/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h299 (by norm_num)) (by norm_num) (by norm_num)
  let v301 : ℝ := v298*v300
  have h301 : Bounds (6873592450264921312735039870012384553517/10000000000000000000000000000000000000000 : ℝ) v301 (6873592450264921312735039870073216353071/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn h298 h300 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j92,hj92⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j91=z := ⟨_,rfl⟩
  have j92_value : Bounds (8363639143457827467032759059691183977931/1250000000000000000000000000000000000000 : ℝ) j92.value (33454556573831309868131036238858513246789/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h297
  have j92_tangent : Bounds (6873592450264921312735039870012384553517/10000000000000000000000000000000000000000 : ℝ) j92.tangent (6873592450264921312735039870073216353071/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj92,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h301
  let v302 : ℝ := j83.value*j77.value
  have h302 : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) v302 (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v303 : ℝ := j83.tangent*j77.value
  have h303 : Bounds (-164810178453389828830806414063/128000000000000000000000000000000 : ℝ) v303 (-1318481427627118630646451312501/1024000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j83_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v304 : ℝ := j83.value*j77.tangent
  have h304 : Bounds (0 : ℝ) v304 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v305 : ℝ := v303+v304
  have h305 : Bounds (-164810178453389828830806414063/128000000000000000000000000000000 : ℝ) v305 (-1318481427627118630646451312501/1024000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h303 h304) (by norm_num) (by norm_num)
  obtain ⟨j93,hj93⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j77=z := ⟨_,rfl⟩
  have j93_value : Bounds (167447141308644066092099316687627/1024000000000000000000000000000000 : ℝ) j93.value (20930892663580508261512414586001/128000000000000000000000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h302
  have j93_tangent : Bounds (-164810178453389828830806414063/128000000000000000000000000000000 : ℝ) j93.tangent (-1318481427627118630646451312501/1024000000000000000000000000000000 : ℝ) := by
    simpa only [← hj93,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h305
  let v306 : ℝ := j92.value*j93.value
  have h306 : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) v306 (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v307 : ℝ := j92.tangent*j93.value
  have h307 : Bounds (561993850740985980916587195188387080921/5000000000000000000000000000000000000000 : ℝ) v307 (224797540296394392366634878077855799099/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j93_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v308 : ℝ := j92.value*j93.tangent
  have h308 : Bounds (-86150803734565062499370932392967330367/10000000000000000000000000000000000000000 : ℝ) v308 (-86150803734565062499370932392529816021/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j93_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v309 : ℝ := v307+v308
  have h309 : Bounds (41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) v309 (518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h307 h308) (by norm_num) (by norm_num)
  obtain ⟨j94,hj94⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j93=z := ⟨_,rfl⟩
  have j94_value : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) j94.value (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h306
  have j94_tangent : Bounds (41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) j94.tangent (518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj94,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h309
  let v310 : ℝ := -j94.value
  have h310 : Bounds (-21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v310 (-10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_value) (by norm_num) (by norm_num)
  let v311 : ℝ := j0.value+v310
  have h311 : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v311 (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h310) (by norm_num) (by norm_num)
  let v312 : ℝ := -j94.tangent
  have h312 : Bounds (-518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) v312 (-41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j94_tangent) (by norm_num) (by norm_num)
  let v313 : ℝ := j0.tangent+v312
  have h313 : Bounds (-518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) v313 (-41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h312) (by norm_num) (by norm_num)
  obtain ⟨j95,hj95⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j94=z := ⟨_,rfl⟩
  have j95_value : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) j95.value (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h311
  have j95_tangent : Bounds (-518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) j95.tangent (-41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj95,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h313
  let v314 : ℝ := j95.value*j41.value
  have h314 : Bounds (-474252412435075855184351505445249114799/10000000000000000000000000000000000000000 : ℝ) v314 (-118563103108768963796087876354312476449/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v315 : ℝ := j95.tangent*j41.value
  have h315 : Bounds (-26148624962776462893371219937808719561/500000000000000000000000000000000000000 : ℝ) v315 (-130743124813882314466856099687413165293/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v316 : ℝ := j95.value*j41.tangent
  have h316 : Bounds (-3676375290194386474297298491823636549/10000000000000000000000000000000000000000 : ℝ) v316 (-3676375290194386474297298491606588417/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j95_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v317 : ℝ := v315+v316
  have h317 : Bounds (-526648874545723644341721697247998027769/10000000000000000000000000000000000000000 : ℝ) v317 (-526648874545723644341721697241259249589/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h315 h316) (by norm_num) (by norm_num)
  obtain ⟨j96,hj96⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j41=z := ⟨_,rfl⟩
  have j96_value : Bounds (-474252412435075855184351505445249114799/10000000000000000000000000000000000000000 : ℝ) j96.value (-118563103108768963796087876354312476449/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h314
  have j96_tangent : Bounds (-526648874545723644341721697247998027769/10000000000000000000000000000000000000000 : ℝ) j96.tangent (-526648874545723644341721697241259249589/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj96,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h317
  let v318 : ℝ := j83.value*j85.value
  have h318 : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) v318 (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j83_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v319 : ℝ := j83.tangent*j85.value
  have h319 : Bounds (225058029918937181370337717503/256000000000000000000000000000000 : ℝ) v319 (180046423935149745096270174003/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j83_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v320 : ℝ := j83.value*j85.tangent
  have h320 : Bounds (0 : ℝ) v320 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j83_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v321 : ℝ := v319+v320
  have h321 : Bounds (225058029918937181370337717503/256000000000000000000000000000000 : ℝ) v321 (180046423935149745096270174003/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h319 h320) (by norm_num) (by norm_num)
  obtain ⟨j97,hj97⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j83 j85=z := ⟨_,rfl⟩
  have j97_value : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) j97.value (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h318
  have j97_tangent : Bounds (225058029918937181370337717503/256000000000000000000000000000000 : ℝ) j97.tangent (180046423935149745096270174003/204800000000000000000000000000000 : ℝ) := by
    simpa only [← hj97,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h321
  let v322 : ℝ := j92.value*j97.value
  have h322 : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) v322 (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v323 : ℝ := j92.tangent*j97.value
  have h323 : Bounds (-767435786195048947689954412637397764629/10000000000000000000000000000000000000000 : ℝ) v323 (-767435786195048947689954412628048441693/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j97_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v324 : ℝ := j92.value*j97.tangent
  have h324 : Bounds (58822004643110183588756775867261345587/10000000000000000000000000000000000000000 : ℝ) v324 (58822004643110183588756775867622253867/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j97_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v325 : ℝ := v323+v324
  have h325 : Bounds (-354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) v325 (-354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h323 h324) (by norm_num) (by norm_num)
  obtain ⟨j98,hj98⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j97=z := ⟨_,rfl⟩
  have j98_value : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) j98.value (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h322
  have j98_tangent : Bounds (-354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) j98.tangent (-354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj98,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h325
  let v326 : ℝ := -j98.value
  have h326 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v326 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_value) (by norm_num) (by norm_num)
  let v327 : ℝ := j6.value+v326
  have h327 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v327 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h326) (by norm_num) (by norm_num)
  let v328 : ℝ := -j98.tangent
  have h328 : Bounds (354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) v328 (354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j98_tangent) (by norm_num) (by norm_num)
  let v329 : ℝ := j6.tangent+v328
  have h329 : Bounds (354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) v329 (354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h328) (by norm_num) (by norm_num)
  obtain ⟨j99,hj99⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j98=z := ⟨_,rfl⟩
  have j99_value : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) j99.value (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h327
  have j99_tangent : Bounds (354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) j99.tangent (354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj99,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h329
  let v330 : ℝ := j99.value*j70.value
  have h330 : Bounds (-1823826804119871414983425423629889219/39062500000000000000000000000000000000 : ℝ) v330 (-466899661854687082235756908446386930599/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v331 : ℝ := j99.tangent*j70.value
  have h331 : Bounds (-44288361346996172756324852298133526191/10000000000000000000000000000000000000000 : ℝ) v331 (-44288361346996172756324852297526636739/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v332 : ℝ := j99.value*j70.tangent
  have h332 : Bounds (-1823826804119871414983425423629889219/39062500000000000000000000000000000000 : ℝ) v332 (-466899661854687082235756908446386930599/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j99_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v333 : ℝ := v331+v332
  have h333 : Bounds (-102237604640336650998416352149477033251/2000000000000000000000000000000000000000 : ℝ) v333 (-255594011600841627496040880371956783669/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h331 h332) (by norm_num) (by norm_num)
  obtain ⟨j100,hj100⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j70=z := ⟨_,rfl⟩
  have j100_value : Bounds (-1823826804119871414983425423629889219/39062500000000000000000000000000000000 : ℝ) j100.value (-466899661854687082235756908446386930599/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h330
  have j100_tangent : Bounds (-102237604640336650998416352149477033251/2000000000000000000000000000000000000000 : ℝ) j100.tangent (-255594011600841627496040880371956783669/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj100,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h333
  let v334 : ℝ := j96.value+j100.value
  have h334 : Bounds (-941152074289762937420108413894500754863/10000000000000000000000000000000000000000 : ℝ) v334 (-188230414857952587484021682772727367279/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_value j100_value) (by norm_num) (by norm_num)
  let v335 : ℝ := j96.tangent+j100.tangent
  have h335 : Bounds (-129729612218425862416725432249422899253/1250000000000000000000000000000000000000 : ℝ) v335 (-1037836897747406899333803457985172816927/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j96_tangent j100_tangent) (by norm_num) (by norm_num)
  obtain ⟨j101,hj101⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j96 j100=z := ⟨_,rfl⟩
  have j101_value : Bounds (-941152074289762937420108413894500754863/10000000000000000000000000000000000000000 : ℝ) j101.value (-188230414857952587484021682772727367279/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h334
  have j101_tangent : Bounds (-129729612218425862416725432249422899253/1250000000000000000000000000000000000000 : ℝ) j101.tangent (-1037836897747406899333803457985172816927/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj101,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h335
  let v336 : ℝ := j92.value*j84.value
  have h336 : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) v336 (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v337 : ℝ := j92.tangent*j84.value
  have h337 : Bounds (561993850740985980916587195188387080921/5000000000000000000000000000000000000000 : ℝ) v337 (224797540296394392366634878077855799099/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j84_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v338 : ℝ := j92.value*j84.tangent
  have h338 : Bounds (-86150803734565062499370932392967330367/10000000000000000000000000000000000000000 : ℝ) v338 (-86150803734565062499370932392529816021/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j84_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v339 : ℝ := v337+v338
  have h339 : Bounds (41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) v339 (518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h337 h338) (by norm_num) (by norm_num)
  obtain ⟨j102,hj102⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j84=z := ⟨_,rfl⟩
  have j102_value : Bounds (10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) j102.value (21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h336
  have j102_tangent : Bounds (41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) j102.tangent (518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj102,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h339
  let v340 : ℝ := -j102.value
  have h340 : Bounds (-21882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v340 (-10941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_value) (by norm_num) (by norm_num)
  let v341 : ℝ := j0.value+v340
  have h341 : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) v341 (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h340) (by norm_num) (by norm_num)
  let v342 : ℝ := -j102.tangent
  have h342 : Bounds (-518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) v342 (-41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j102_tangent) (by norm_num) (by norm_num)
  let v343 : ℝ := j0.tangent+v342
  have h343 : Bounds (-518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) v343 (-41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h342) (by norm_num) (by norm_num)
  obtain ⟨j103,hj103⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j102=z := ⟨_,rfl⟩
  have j103_value : Bounds (-1882304148579525874840216827813701913/20000000000000000000000000000000000000 : ℝ) j103.value (-941152074289762937420108413851286634759/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h341
  have j103_tangent : Bounds (-518918448873703449666901728998374589737/5000000000000000000000000000000000000000 : ℝ) j103.tangent (-41513475909896275973352138319352273259/400000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj103,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h343
  let v344 : ℝ := j101.value*j103.value
  have h344 : Bounds (88576722693992345512649704591593057051/10000000000000000000000000000000000000000 : ℝ) v344 (88576722693992345512649704599727268807/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v345 : ℝ := j101.tangent*j103.value
  have h345 : Bounds (763095585226112968347015361738395749/78125000000000000000000000000000000000 : ℝ) v345 (97676234908942459948417966309242277961/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v346 : ℝ := j101.value*j103.tangent
  have h346 : Bounds (97676234908942459948417966303667845363/10000000000000000000000000000000000000000 : ℝ) v346 (9767623490894245994841796630808908847/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v347 : ℝ := v345+v346
  have h347 : Bounds (39070493963576983979367186521236500247/2000000000000000000000000000000000000000 : ℝ) v347 (195352469817884919896835932617331366431/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h345 h346) (by norm_num) (by norm_num)
  obtain ⟨j104,hj104⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j103=z := ⟨_,rfl⟩
  have j104_value : Bounds (88576722693992345512649704591593057051/10000000000000000000000000000000000000000 : ℝ) j104.value (88576722693992345512649704599727268807/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h344
  have j104_tangent : Bounds (39070493963576983979367186521236500247/2000000000000000000000000000000000000000 : ℝ) j104.tangent (195352469817884919896835932617331366431/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj104,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h347
  let v348 : ℝ := j95.value*j52.value
  have h348 : Bounds (3676375290194386474297298491606588417/625000000000000000000000000000000000000 : ℝ) v348 (29411002321555091794378387934589092391/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v349 : ℝ := j95.tangent*j52.value
  have h349 : Bounds (64864806109212931208362716123987926967/10000000000000000000000000000000000000000 : ℝ) v349 (32432403054606465604181358062398411859/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v350 : ℝ := j95.value*j52.tangent
  have h350 : Bounds (3676375290194386474297298491606588417/625000000000000000000000000000000000000 : ℝ) v350 (29411002321555091794378387934589092391/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j95_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v351 : ℝ := v349+v350
  have h351 : Bounds (123686810752323114797119491989693341639/10000000000000000000000000000000000000000 : ℝ) v351 (247373621504646229594238983987950017/20000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h349 h350) (by norm_num) (by norm_num)
  obtain ⟨j105,hj105⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j95 j52=z := ⟨_,rfl⟩
  have j105_value : Bounds (3676375290194386474297298491606588417/625000000000000000000000000000000000000 : ℝ) j105.value (29411002321555091794378387934589092391/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h348
  have j105_tangent : Bounds (123686810752323114797119491989693341639/10000000000000000000000000000000000000000 : ℝ) j105.tangent (247373621504646229594238983987950017/20000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj105,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h351
  let v352 : ℝ := j99.value*j76.value
  have h352 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v352 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v353 : ℝ := j99.tangent*j76.value
  have h353 : Bounds (354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) v353 (354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v354 : ℝ := j99.value*j76.tangent
  have h354 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v354 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j99_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v355 : ℝ := v353+v354
  have h355 : Bounds (1022376046403366509984163521487827134677/1250000000000000000000000000000000000000 : ℝ) v355 (1635801674245386415974661634391632532013/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h353 h354) (by norm_num) (by norm_num)
  obtain ⟨j106,hj106⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j99 j76=z := ⟨_,rfl⟩
  have j106_value : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) j106.value (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h352
  have j106_tangent : Bounds (1022376046403366509984163521487827134677/1250000000000000000000000000000000000000 : ℝ) j106.tangent (1635801674245386415974661634391632532013/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj106,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h355
  let v356 : ℝ := j105.value+j106.value
  have h356 : Bounds (3764608297159051749680433655503948152131/5000000000000000000000000000000000000000 : ℝ) v356 (1505843318863620699872173462211440885161/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_value j106_value) (by norm_num) (by norm_num)
  let v357 : ℝ := j105.tangent+j106.tangent
  have h357 : Bounds (1660539036395851038934085532778462083811/2000000000000000000000000000000000000000 : ℝ) v357 (1660539036395851038934085532790427533713/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j105_tangent j106_tangent) (by norm_num) (by norm_num)
  obtain ⟨j107,hj107⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j105 j106=z := ⟨_,rfl⟩
  have j107_value : Bounds (3764608297159051749680433655503948152131/5000000000000000000000000000000000000000 : ℝ) j107.value (1505843318863620699872173462211440885161/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h356
  have j107_tangent : Bounds (1660539036395851038934085532778462083811/2000000000000000000000000000000000000000 : ℝ) j107.tangent (1660539036395851038934085532790427533713/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj107,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h357
  let v358 : ℝ := j85.value*j83.value
  have h358 : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) v358 (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j85_value j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v359 : ℝ := j85.tangent*j83.value
  have h359 : Bounds (0 : ℝ) v359 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j85_tangent j83_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v360 : ℝ := j85.value*j83.tangent
  have h360 : Bounds (225058029918937181370337717503/256000000000000000000000000000000 : ℝ) v360 (180046423935149745096270174003/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j85_value j83_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v361 : ℝ := v359+v360
  have h361 : Bounds (225058029918937181370337717503/256000000000000000000000000000000 : ℝ) v361 (180046423935149745096270174003/204800000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h359 h360) (by norm_num) (by norm_num)
  obtain ⟨j108,hj108⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j85 j83=z := ⟨_,rfl⟩
  have j108_value : Bounds (-22865895839764017627226312098381/204800000000000000000000000000000 : ℝ) j108.value (-28582369799705022034032890122881/256000000000000000000000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h358
  have j108_tangent : Bounds (225058029918937181370337717503/256000000000000000000000000000000 : ℝ) j108.tangent (180046423935149745096270174003/204800000000000000000000000000000 : ℝ) := by
    simpa only [← hj108,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h361
  let v362 : ℝ := j92.value*j108.value
  have h362 : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) v362 (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v363 : ℝ := j92.tangent*j108.value
  have h363 : Bounds (-767435786195048947689954412637397764629/10000000000000000000000000000000000000000 : ℝ) v363 (-767435786195048947689954412628048441693/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j108_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v364 : ℝ := j92.value*j108.tangent
  have h364 : Bounds (58822004643110183588756775867261345587/10000000000000000000000000000000000000000 : ℝ) v364 (58822004643110183588756775867622253867/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j108_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v365 : ℝ := v363+v364
  have h365 : Bounds (-354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) v365 (-354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h363 h364) (by norm_num) (by norm_num)
  obtain ⟨j109,hj109⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j108=z := ⟨_,rfl⟩
  have j109_value : Bounds (-7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) j109.value (-747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h362
  have j109_tangent : Bounds (-354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) j109.tangent (-354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj109,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h365
  let v366 : ℝ := -j109.value
  have h366 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v366 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_value) (by norm_num) (by norm_num)
  let v367 : ℝ := j6.value+v366
  have h367 : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) v367 (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h366) (by norm_num) (by norm_num)
  let v368 : ℝ := -j109.tangent
  have h368 : Bounds (354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) v368 (354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j109_tangent) (by norm_num) (by norm_num)
  let v369 : ℝ := j6.tangent+v368
  have h369 : Bounds (354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) v369 (354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h368) (by norm_num) (by norm_num)
  obtain ⟨j110,hj110⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j109=z := ⟨_,rfl⟩
  have j110_value : Bounds (747039458967499331577211053514219088959/1000000000000000000000000000000000000000 : ℝ) j110.value (7470394589674993315772110535188026241023/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h367
  have j110_tangent : Bounds (354306890775969382050598818380213093913/5000000000000000000000000000000000000000 : ℝ) j110.tangent (354306890775969382050598818385068209521/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj110,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h369
  let v370 : ℝ := j107.value*j110.value
  have h370 : Bounds (562462189106851394005325624178874757537/1000000000000000000000000000000000000000 : ℝ) v370 (5624621891068513940053256241860093116673/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v371 : ℝ := j107.tangent*j110.value
  have h371 : Bounds (6202440916717846206724540860381908143571/10000000000000000000000000000000000000000 : ℝ) v371 (1550610229179461551681135215116164288707/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v372 : ℝ := j107.value*j110.tangent
  have h372 : Bounds (533530664302336093914959766295629679289/10000000000000000000000000000000000000000 : ℝ) v372 (266765332151168046957479883153217382069/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v373 : ℝ := v371+v372
  have h373 : Bounds (336798579051009115031975031333876891143/500000000000000000000000000000000000000 : ℝ) v373 (3367985790510091150319750313385545959483/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h371 h372) (by norm_num) (by norm_num)
  obtain ⟨j111,hj111⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j110=z := ⟨_,rfl⟩
  have j111_value : Bounds (562462189106851394005325624178874757537/1000000000000000000000000000000000000000 : ℝ) j111.value (5624621891068513940053256241860093116673/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h370
  have j111_tangent : Bounds (336798579051009115031975031333876891143/500000000000000000000000000000000000000 : ℝ) j111.tangent (3367985790510091150319750313385545959483/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj111,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h373
  let v374 : ℝ := j104.value+j111.value
  have h374 : Bounds (5713198613762506285565905946380340632421/10000000000000000000000000000000000000000 : ℝ) v374 (142829965344062657139147648661495509637/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_value j111_value) (by norm_num) (by norm_num)
  let v375 : ℝ := j104.tangent+j111.tangent
  have h375 : Bounds (1386264810167613444107267311856744064819/2000000000000000000000000000000000000000 : ℝ) v375 (6931324050838067220536336559388423285397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j104_tangent j111_tangent) (by norm_num) (by norm_num)
  obtain ⟨j112,hj112⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j104 j111=z := ⟨_,rfl⟩
  have j112_value : Bounds (5713198613762506285565905946380340632421/10000000000000000000000000000000000000000 : ℝ) j112.value (142829965344062657139147648661495509637/250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj112,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h374
  have j112_tangent : Bounds (1386264810167613444107267311856744064819/2000000000000000000000000000000000000000 : ℝ) j112.tangent (6931324050838067220536336559388423285397/10000000000000000000000000000000000000000 : ℝ) := by
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
  have h380 : Bounds (205836693946580961938127702138914652069/2000000000000000000000000000000000000000 : ℝ) v380 (1029183469732904809690638510697458191219/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v381 : ℝ := j92.tangent*j113.value
  have h381 : Bounds (4229132561886707910656107256447973269/400000000000000000000000000000000000000 : ℝ) v381 (52864157023583848883201340706067517547/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j113_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v382 : ℝ := j92.value*j113.tangent
  have h382 : Bounds (-16207613696581178105364385995235562067/10000000000000000000000000000000000000000 : ℝ) v382 (-4051903424145294526341096498797532521/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j113_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v383 : ℝ := v381+v382
  have h383 : Bounds (44760350175293259830519147707981884829/5000000000000000000000000000000000000000 : ℝ) v383 (8952070035058651966103829541694490501/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h381 h382) (by norm_num) (by norm_num)
  obtain ⟨j114,hj114⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j113=z := ⟨_,rfl⟩
  have j114_value : Bounds (205836693946580961938127702138914652069/2000000000000000000000000000000000000000 : ℝ) j114.value (1029183469732904809690638510697458191219/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h380
  have j114_tangent : Bounds (44760350175293259830519147707981884829/5000000000000000000000000000000000000000 : ℝ) j114.tangent (8952070035058651966103829541694490501/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj114,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h383
  let v384 : ℝ := j112.value+j114.value
  have h384 : Bounds (3371191041747705547628272228537456946383/5000000000000000000000000000000000000000 : ℝ) v384 (6742382083495411095256544457157278576699/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_value j114_value) (by norm_num) (by norm_num)
  let v385 : ℝ := j112.tangent+j114.tangent
  have h385 : Bounds (7020844751188653740197374854699684093753/10000000000000000000000000000000000000000 : ℝ) v385 (7020844751188653740197374854805368190407/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j112_tangent j114_tangent) (by norm_num) (by norm_num)
  obtain ⟨j115,hj115⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j112 j114=z := ⟨_,rfl⟩
  have j115_value : Bounds (3371191041747705547628272228537456946383/5000000000000000000000000000000000000000 : ℝ) j115.value (6742382083495411095256544457157278576699/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h384
  have j115_tangent : Bounds (7020844751188653740197374854699684093753/10000000000000000000000000000000000000000 : ℝ) j115.tangent (7020844751188653740197374854805368190407/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj115,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h385
  let v386 : ℝ := j77.value*j89.value
  have h386 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v386 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v387 : ℝ := j77.tangent*j89.value
  have h387 : Bounds (0 : ℝ) v387 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_tangent j89_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v388 : ℝ := j77.value*j89.tangent
  have h388 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v388 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j77_value j89_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v389 : ℝ := v387+v388
  have h389 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v389 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h387 h388) (by norm_num) (by norm_num)
  obtain ⟨j116,hj116⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j77 j89=z := ⟨_,rfl⟩
  have j116_value : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) j116.value (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h386
  have j116_tangent : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) j116.tangent (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    simpa only [← hj116,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h389
  let v390 : ℝ := j92.value*j116.value
  have h390 : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) v390 (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v391 : ℝ := j92.tangent*j116.value
  have h391 : Bounds (17700593724125542706034242368138175777/1250000000000000000000000000000000000000 : ℝ) v391 (141604749793004341648273938946680818331/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j116_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v392 : ℝ := j92.value*j116.tangent
  have h392 : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) v392 (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j116_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v393 : ℝ := v391+v392
  have h393 : Bounds (1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) v393 (152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h391 h392) (by norm_num) (by norm_num)
  obtain ⟨j117,hj117⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j116=z := ⟨_,rfl⟩
  have j117_value : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) j117.value (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h390
  have j117_tangent : Bounds (1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) j117.tangent (152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj117,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h393
  let v394 : ℝ := -j117.value
  have h394 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v394 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_value) (by norm_num) (by norm_num)
  let v395 : ℝ := j6.value+v394
  have h395 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v395 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h394) (by norm_num) (by norm_num)
  let v396 : ℝ := -j117.tangent
  have h396 : Bounds (-152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) v396 (-1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j117_tangent) (by norm_num) (by norm_num)
  let v397 : ℝ := j6.tangent+v396
  have h397 : Bounds (-152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) v397 (-1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h396) (by norm_num) (by norm_num)
  obtain ⟨j118,hj118⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j117=z := ⟨_,rfl⟩
  have j118_value : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) j118.value (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h395
  have j118_tangent : Bounds (-152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) j118.tangent (-1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj118,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h397
  let v398 : ℝ := j101.value*j118.value
  have h398 : Bounds (2027025190912904100261334878848877743/156250000000000000000000000000000000000 : ℝ) v398 (129729612218425862416725432251241325817/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v399 : ℝ := j101.tangent*j118.value
  have h399 : Bounds (143056772618122753925319234555929130431/10000000000000000000000000000000000000000 : ℝ) v399 (143056772618122753925319234558063051589/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v400 : ℝ := j101.value*j118.tangent
  have h400 : Bounds (71528386309061376962659617277123428443/5000000000000000000000000000000000000000 : ℝ) v400 (71528386309061376962659617279872662567/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j101_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v401 : ℝ := v399+v400
  have h401 : Bounds (286113545236245507850638469110175987317/10000000000000000000000000000000000000000 : ℝ) v401 (286113545236245507850638469117808376723/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h399 h400) (by norm_num) (by norm_num)
  obtain ⟨j119,hj119⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j101 j118=z := ⟨_,rfl⟩
  have j119_value : Bounds (2027025190912904100261334878848877743/156250000000000000000000000000000000000 : ℝ) j119.value (129729612218425862416725432251241325817/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h398
  have j119_tangent : Bounds (286113545236245507850638469110175987317/10000000000000000000000000000000000000000 : ℝ) j119.tangent (286113545236245507850638469117808376723/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj119,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h401
  let v402 : ℝ := j92.value*j90.value
  have h402 : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) v402 (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v403 : ℝ := j92.tangent*j90.value
  have h403 : Bounds (-12085602932205495239211880513974767947/1250000000000000000000000000000000000000 : ℝ) v403 (-48342411728821980956847522055310138059/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j90_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v404 : ℝ := j92.value*j90.tangent
  have h404 : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) v404 (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j90_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v405 : ℝ := v403+v404
  have h405 : Bounds (-518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) v405 (-207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h403 h404) (by norm_num) (by norm_num)
  obtain ⟨j120,hj120⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j90=z := ⟨_,rfl⟩
  have j120_value : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) j120.value (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h402
  have j120_tangent : Bounds (-518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) j120.tangent (-207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj120,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h405
  let v406 : ℝ := -j120.value
  have h406 : Bounds (941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v406 (470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_value) (by norm_num) (by norm_num)
  let v407 : ℝ := j0.value+v406
  have h407 : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v407 (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h406) (by norm_num) (by norm_num)
  let v408 : ℝ := -j120.tangent
  have h408 : Bounds (207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) v408 (518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j120_tangent) (by norm_num) (by norm_num)
  let v409 : ℝ := j0.tangent+v408
  have h409 : Bounds (207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) v409 (518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h408) (by norm_num) (by norm_num)
  obtain ⟨j121,hj121⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j120=z := ⟨_,rfl⟩
  have j121_value : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) j121.value (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h407
  have j121_tangent : Bounds (207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) j121.tangent (518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj121,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h409
  let v410 : ℝ := j107.value*j121.value
  have h410 : Bounds (8237830375870042263462064947768683400371/10000000000000000000000000000000000000000 : ℝ) v410 (1029728796983755282932758118478372492071/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v411 : ℝ := j107.tangent*j121.value
  have h411 : Bounds (2271026265312698718564442848583531404561/2500000000000000000000000000000000000000 : ℝ) v411 (9084105061250794874257771394404377940041/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v412 : ℝ := j107.value*j121.tangent
  have h412 : Bounds (390704939635769839793671865220925869847/5000000000000000000000000000000000000000 : ℝ) v412 (781409879271539679587343730452203730971/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j107_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v413 : ℝ := v411+v412
  have h413 : Bounds (4932757470261167276922557562387988678969/5000000000000000000000000000000000000000 : ℝ) v413 (2466378735130583638461278781214145417753/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h411 h412) (by norm_num) (by norm_num)
  obtain ⟨j122,hj122⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j107 j121=z := ⟨_,rfl⟩
  have j122_value : Bounds (8237830375870042263462064947768683400371/10000000000000000000000000000000000000000 : ℝ) j122.value (1029728796983755282932758118478372492071/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h410
  have j122_tangent : Bounds (4932757470261167276922557562387988678969/5000000000000000000000000000000000000000 : ℝ) j122.tangent (2466378735130583638461278781214145417753/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj122,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h413
  let v414 : ℝ := j119.value+j122.value
  have h414 : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) v414 (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_value j122_value) (by norm_num) (by norm_num)
  let v415 : ℝ := j119.tangent+j122.tangent
  have h415 : Bounds (2030325697151716012339150718777230669051/2000000000000000000000000000000000000000 : ℝ) v415 (2030325697151716012339150718794878009547/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j119_tangent j122_tangent) (by norm_num) (by norm_num)
  obtain ⟨j123,hj123⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j119 j122=z := ⟨_,rfl⟩
  have j123_value : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) j123.value (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj123,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h414
  have j123_tangent : Bounds (2030325697151716012339150718777230669051/2000000000000000000000000000000000000000 : ℝ) j123.tangent (2030325697151716012339150718794878009547/2000000000000000000000000000000000000000 : ℝ) := by
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
  have h420 : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) v420 (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v421 : ℝ := j92.tangent*j124.value
  have h421 : Bounds (2664020511424697896476288035557778437/2000000000000000000000000000000000000000 : ℝ) v421 (532804102284939579295257607116271043/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j124_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v422 : ℝ := j92.value*j124.tangent
  have h422 : Bounds (128639957528770295513443315615367331691/10000000000000000000000000000000000000000 : ℝ) v422 (128639957528770295513443315615727925693/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j124_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v423 : ℝ := v421+v422
  have h423 : Bounds (35490015021473446248956188948289055969/2500000000000000000000000000000000000000 : ℝ) v423 (17745007510736723124478094474204337721/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h421 h422) (by norm_num) (by norm_num)
  obtain ⟨j125,hj125⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j124=z := ⟨_,rfl⟩
  have j125_value : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) j125.value (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h420
  have j125_tangent : Bounds (35490015021473446248956188948289055969/2500000000000000000000000000000000000000 : ℝ) j125.tangent (17745007510736723124478094474204337721/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj125,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h423
  let v424 : ℝ := j123.value+j125.value
  have h424 : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) v424 (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_value j125_value) (by norm_num) (by norm_num)
  let v425 : ℝ := j123.tangent+j125.tangent
  have h425 : Bounds (10293588545844473846691578349679309569131/10000000000000000000000000000000000000000 : ℝ) v425 (10293588545844473846691578349768024749503/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j123_tangent j125_tangent) (by norm_num) (by norm_num)
  obtain ⟨j126,hj126⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j123 j125=z := ⟨_,rfl⟩
  have j126_value : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) j126.value (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h424
  have j126_tangent : Bounds (10293588545844473846691578349679309569131/10000000000000000000000000000000000000000 : ℝ) j126.tangent (10293588545844473846691578349768024749503/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj126,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h425
  let v426 : ℝ := j89.value*j77.value
  have h426 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v426 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v427 : ℝ := j89.tangent*j77.value
  have h427 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v427 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_tangent j77_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v428 : ℝ := j89.value*j77.tangent
  have h428 : Bounds (0 : ℝ) v428 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j77_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v429 : ℝ := v427+v428
  have h429 : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) v429 (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h427 h428) (by norm_num) (by norm_num)
  obtain ⟨j127,hj127⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j77=z := ⟨_,rfl⟩
  have j127_value : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) j127.value (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h426
  have j127_tangent : Bounds (1318481427627118630646451312501/64000000000000000000000000000000 : ℝ) j127.tangent (164810178453389828830806414063/8000000000000000000000000000000 : ℝ) := by
    simpa only [← hj127,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h429
  let v430 : ℝ := j92.value*j127.value
  have h430 : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) v430 (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v431 : ℝ := j92.tangent*j127.value
  have h431 : Bounds (17700593724125542706034242368138175777/1250000000000000000000000000000000000000 : ℝ) v431 (141604749793004341648273938946680818331/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j127_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v432 : ℝ := j92.value*j127.tangent
  have h432 : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) v432 (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j127_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v433 : ℝ := v431+v432
  have h433 : Bounds (1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) v433 (152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h431 h432) (by norm_num) (by norm_num)
  obtain ⟨j128,hj128⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j127=z := ⟨_,rfl⟩
  have j128_value : Bounds (1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) j128.value (1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h430
  have j128_tangent : Bounds (1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) j128.tangent (152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj128,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h433
  let v434 : ℝ := -j128.value
  have h434 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v434 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_value) (by norm_num) (by norm_num)
  let v435 : ℝ := j6.value+v434
  have h435 : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) v435 (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h434) (by norm_num) (by norm_num)
  let v436 : ℝ := -j128.tangent
  have h436 : Bounds (-152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) v436 (-1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j128_tangent) (by norm_num) (by norm_num)
  let v437 : ℝ := j6.tangent+v436
  have h437 : Bounds (-152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) v437 (-1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h436) (by norm_num) (by norm_num)
  obtain ⟨j129,hj129⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j128=z := ⟨_,rfl⟩
  have j129_value : Bounds (-1378412859753040999989934918287477285859/10000000000000000000000000000000000000000 : ℝ) j129.value (-1378412859753040999989934918280477056347/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h435
  have j129_tangent : Bounds (-152001760954604534163820885723415810419/1000000000000000000000000000000000000000 : ℝ) j129.tangent (-1520017609546045341638208857225582462563/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj129,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h437
  let v438 : ℝ := j129.value*j41.value
  have h438 : Bounds (-347295427554965408200589071209149550539/5000000000000000000000000000000000000000 : ℝ) v438 (-347295427554965408200589071207385820837/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v439 : ℝ := j129.tangent*j41.value
  have h439 : Bounds (-76594637356031191043487868196564998219/1000000000000000000000000000000000000000 : ℝ) v439 (-30637854942412476417395147278453146511/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_tangent j41_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v440 : ℝ := j129.value*j41.tangent
  have h440 : Bounds (-1346106308352579101552670818640114537/2500000000000000000000000000000000000000 : ℝ) v440 (-5384425233410316406210683274533113501/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j129_value j41_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v441 : ℝ := v439+v440
  have h441 : Bounds (-385665399396861113420544682620105220169/5000000000000000000000000000000000000000 : ℝ) v441 (-192832699698430556710272341308965444069/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h439 h440) (by norm_num) (by norm_num)
  obtain ⟨j130,hj130⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j41=z := ⟨_,rfl⟩
  have j130_value : Bounds (-347295427554965408200589071209149550539/5000000000000000000000000000000000000000 : ℝ) j130.value (-347295427554965408200589071207385820837/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h438
  have j130_tangent : Bounds (-385665399396861113420544682620105220169/5000000000000000000000000000000000000000 : ℝ) j130.tangent (-192832699698430556710272341308965444069/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj130,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h441
  let v442 : ℝ := j89.value*j85.value
  have h442 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v442 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_value j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v443 : ℝ := j89.tangent*j85.value
  have h443 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v443 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j89_tangent j85_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v444 : ℝ := j89.value*j85.tangent
  have h444 : Bounds (0 : ℝ) v444 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j89_value j85_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v445 : ℝ := v443+v444
  have h445 : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) v445 (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h443 h444) (by norm_num) (by norm_num)
  obtain ⟨j131,hj131⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j89 j85=z := ⟨_,rfl⟩
  have j131_value : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) j131.value (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h442
  have j131_tangent : Bounds (-180046423935149745096270174003/12800000000000000000000000000000 : ℝ) j131.tangent (-225058029918937181370337717503/16000000000000000000000000000000 : ℝ) := by
    simpa only [← hj131,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h445
  let v446 : ℝ := j92.value*j131.value
  have h446 : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) v446 (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v447 : ℝ := j92.tangent*j131.value
  have h447 : Bounds (-12085602932205495239211880513974767947/1250000000000000000000000000000000000000 : ℝ) v447 (-48342411728821980956847522055310138059/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_tangent j131_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v448 : ℝ := j92.value*j131.tangent
  have h448 : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) v448 (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j92_value j131_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v449 : ℝ := v447+v448
  have h449 : Bounds (-518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) v449 (-207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h447 h448) (by norm_num) (by norm_num)
  obtain ⟨j132,hj132⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j131=z := ⟨_,rfl⟩
  have j132_value : Bounds (-470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) j132.value (-941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h446
  have j132_tangent : Bounds (-518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) j132.tangent (-207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj132,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h449
  let v450 : ℝ := -j132.value
  have h450 : Bounds (941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v450 (470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_value) (by norm_num) (by norm_num)
  let v451 : ℝ := j0.value+v450
  have h451 : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v451 (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h450) (by norm_num) (by norm_num)
  let v452 : ℝ := -j132.tangent
  have h452 : Bounds (207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) v452 (518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j132_tangent) (by norm_num) (by norm_num)
  let v453 : ℝ := j0.tangent+v452
  have h453 : Bounds (207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) v453 (518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h452) (by norm_num) (by norm_num)
  obtain ⟨j133,hj133⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j132=z := ⟨_,rfl⟩
  have j133_value : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) j133.value (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h451
  have j133_tangent : Bounds (207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) j133.tangent (518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj133,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h453
  let v454 : ℝ := j133.value*j70.value
  have h454 : Bounds (-683822004643110183588756775867622253867/10000000000000000000000000000000000000000 : ℝ) v454 (-683822004643110183588756775867261345587/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v455 : ℝ := j133.tangent*j70.value
  have h455 : Bounds (-810810076365161640104533951557620473/125000000000000000000000000000000000000 : ℝ) v455 (-16216201527303232802090679031043778211/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_tangent j70_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v456 : ℝ := j133.value*j70.tangent
  have h456 : Bounds (-683822004643110183588756775867622253867/10000000000000000000000000000000000000000 : ℝ) v456 (-683822004643110183588756775867261345587/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j133_value j70_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v457 : ℝ := v455+v456
  have h457 : Bounds (-748686810752323114797119491992231891707/10000000000000000000000000000000000000000 : ℝ) v457 (-748686810752323114797119491991436458431/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h455 h456) (by norm_num) (by norm_num)
  obtain ⟨j134,hj134⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j70=z := ⟨_,rfl⟩
  have j134_value : Bounds (-683822004643110183588756775867622253867/10000000000000000000000000000000000000000 : ℝ) j134.value (-683822004643110183588756775867261345587/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h454
  have j134_tangent : Bounds (-748686810752323114797119491992231891707/10000000000000000000000000000000000000000 : ℝ) j134.tangent (-748686810752323114797119491991436458431/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj134,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h457
  let v458 : ℝ := j130.value+j134.value
  have h458 : Bounds (-275682571950608199997986983657184270989/2000000000000000000000000000000000000000 : ℝ) v458 (-1378412859753040999989934918282032987261/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_value j134_value) (by norm_num) (by norm_num)
  let v459 : ℝ := j130.tangent+j134.tangent
  have h459 : Bounds (-304003521909209068327641771446488466409/2000000000000000000000000000000000000000 : ℝ) v459 (-1520017609546045341638208857227298234707/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j130_tangent j134_tangent) (by norm_num) (by norm_num)
  obtain ⟨j135,hj135⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j130 j134=z := ⟨_,rfl⟩
  have j135_value : Bounds (-275682571950608199997986983657184270989/2000000000000000000000000000000000000000 : ℝ) j135.value (-1378412859753040999989934918282032987261/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h458
  have j135_tangent : Bounds (-304003521909209068327641771446488466409/2000000000000000000000000000000000000000 : ℝ) j135.tangent (-1520017609546045341638208857227298234707/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj135,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h459
  let v460 : ℝ := j135.value*j103.value
  have h460 : Bounds (129729612218425862416725432244772244637/10000000000000000000000000000000000000000 : ℝ) v460 (32432403054606465604181358063199314183/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v461 : ℝ := j135.tangent*j103.value
  have h461 : Bounds (7152838630906137696265961727626554237/500000000000000000000000000000000000000 : ℝ) v461 (447052414431633606016622608004565929/31250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j103_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v462 : ℝ := j135.value*j103.tangent
  have h462 : Bounds (143056772618122753925319234555902321491/10000000000000000000000000000000000000000 : ℝ) v462 (143056772618122753925319234558089860529/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j103_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v463 : ℝ := v461+v462
  have h463 : Bounds (286113545236245507850638469108433406231/10000000000000000000000000000000000000000 : ℝ) v463 (286113545236245507850638469119550957809/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h461 h462) (by norm_num) (by norm_num)
  obtain ⟨j136,hj136⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j103=z := ⟨_,rfl⟩
  have j136_value : Bounds (129729612218425862416725432244772244637/10000000000000000000000000000000000000000 : ℝ) j136.value (32432403054606465604181358063199314183/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h460
  have j136_tangent : Bounds (286113545236245507850638469108433406231/10000000000000000000000000000000000000000 : ℝ) j136.tangent (286113545236245507850638469119550957809/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj136,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h463
  let v464 : ℝ := j129.value*j52.value
  have h464 : Bounds (86150803734565062499370932392529816021/10000000000000000000000000000000000000000 : ℝ) v464 (86150803734565062499370932392967330367/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v465 : ℝ := j129.tangent*j52.value
  have h465 : Bounds (9500110059662783385238805357659890391/1000000000000000000000000000000000000000 : ℝ) v465 (11875137574578479231548506697141860189/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_tangent j52_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v466 : ℝ := j129.value*j52.tangent
  have h466 : Bounds (86150803734565062499370932392529816021/10000000000000000000000000000000000000000 : ℝ) v466 (86150803734565062499370932392967330367/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j129_value j52_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v467 : ℝ := v465+v466
  have h467 : Bounds (181151904331192896351758985969128719931/10000000000000000000000000000000000000000 : ℝ) v467 (181151904331192896351758985970102211879/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h465 h466) (by norm_num) (by norm_num)
  obtain ⟨j137,hj137⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j129 j52=z := ⟨_,rfl⟩
  have j137_value : Bounds (86150803734565062499370932392529816021/10000000000000000000000000000000000000000 : ℝ) j137.value (86150803734565062499370932392967330367/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h464
  have j137_tangent : Bounds (181151904331192896351758985969128719931/10000000000000000000000000000000000000000 : ℝ) j137.tangent (181151904331192896351758985970102211879/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj137,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h467
  let v468 : ℝ := j133.value*j76.value
  have h468 : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v468 (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v469 : ℝ := j133.tangent*j76.value
  have h469 : Bounds (207567379549481379866760691597360361103/2000000000000000000000000000000000000000 : ℝ) v469 (518918448873703449666901728996877102719/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_tangent j76_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v470 : ℝ := j133.value*j76.tangent
  have h470 : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) v470 (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j133_value j76_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v471 : ℝ := v469+v470
  have h471 : Bounds (11698231418005048668704992062366194663/9765625000000000000000000000000000000 : ℝ) v471 (119789889720371698367539118718757102673/100000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h469 h470) (by norm_num) (by norm_num)
  obtain ⟨j138,hj138⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j133 j76=z := ⟨_,rfl⟩
  have j138_value : Bounds (10941152074289762937420108413876181529397/10000000000000000000000000000000000000000 : ℝ) j138.value (5470576037144881468710054206940978030931/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h468
  have j138_tangent : Bounds (11698231418005048668704992062366194663/9765625000000000000000000000000000000 : ℝ) j138.tangent (119789889720371698367539118718757102673/100000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj138,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h471
  let v472 : ℝ := j137.value+j138.value
  have h472 : Bounds (5513651439012163999959739673134355672709/5000000000000000000000000000000000000000 : ℝ) v472 (11027302878024327999919479346274923392229/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_value j138_value) (by norm_num) (by norm_num)
  let v473 : ℝ := j137.tangent+j138.tangent
  have h473 : Bounds (12160140876368362733105670857832112054843/10000000000000000000000000000000000000000 : ℝ) v473 (12160140876368362733105670857845812479179/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j137_tangent j138_tangent) (by norm_num) (by norm_num)
  obtain ⟨j139,hj139⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j137 j138=z := ⟨_,rfl⟩
  have j139_value : Bounds (5513651439012163999959739673134355672709/5000000000000000000000000000000000000000 : ℝ) j139.value (11027302878024327999919479346274923392229/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h472
  have j139_tangent : Bounds (12160140876368362733105670857832112054843/10000000000000000000000000000000000000000 : ℝ) j139.tangent (12160140876368362733105670857845812479179/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj139,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h473
  let v474 : ℝ := j139.value*j110.value
  have h474 : Bounds (4118915187935021131731032473885119665643/5000000000000000000000000000000000000000 : ℝ) v474 (8237830375870042263462064947825424005653/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v475 : ℝ := j139.tangent*j110.value
  have h475 : Bounds (363364202450031794970310855773450647353/400000000000000000000000000000000000000 : ℝ) v475 (9084105061250794874257771394402237374463/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j110_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v476 : ℝ := j139.value*j110.tangent
  have h476 : Bounds (781409879271539679587343730441453755199/10000000000000000000000000000000000000000 : ℝ) v476 (390704939635769839793671865226300857731/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j110_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v477 : ℝ := v475+v476
  have h477 : Bounds (616594683782645909615319695298607496189/625000000000000000000000000000000000000 : ℝ) v477 (394620597620893382153804604994193563597/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h475 h476) (by norm_num) (by norm_num)
  obtain ⟨j140,hj140⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j110=z := ⟨_,rfl⟩
  have j140_value : Bounds (4118915187935021131731032473885119665643/5000000000000000000000000000000000000000 : ℝ) j140.value (8237830375870042263462064947825424005653/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h474
  have j140_tangent : Bounds (616594683782645909615319695298607496189/625000000000000000000000000000000000000 : ℝ) j140.tangent (394620597620893382153804604994193563597/400000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj140,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h477
  let v478 : ℝ := j136.value+j140.value
  have h478 : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) v478 (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_value j140_value) (by norm_num) (by norm_num)
  let v479 : ℝ := j136.tangent+j140.tangent
  have h479 : Bounds (2030325697151716012339150718777230669051/2000000000000000000000000000000000000000 : ℝ) v479 (5075814242879290030847876796987195023867/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j136_tangent j140_tangent) (by norm_num) (by norm_num)
  obtain ⟨j141,hj141⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j136 j140=z := ⟨_,rfl⟩
  have j141_value : Bounds (8367559988088468125878790380015011575923/10000000000000000000000000000000000000000 : ℝ) j141.value (1673511997617693625175758076015644252477/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj141,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h478
  have j141_tangent : Bounds (2030325697151716012339150718777230669051/2000000000000000000000000000000000000000 : ℝ) j141.tangent (5075814242879290030847876796987195023867/5000000000000000000000000000000000000000 : ℝ) := by
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
  have h484 : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) v484 (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v485 : ℝ := j92.tangent*j142.value
  have h485 : Bounds (2664020511424697896476288035557778437/2000000000000000000000000000000000000000 : ℝ) v485 (532804102284939579295257607116271043/400000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j142_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v486 : ℝ := j92.value*j142.tangent
  have h486 : Bounds (128639957528770295513443315615367331691/10000000000000000000000000000000000000000 : ℝ) v486 (128639957528770295513443315615727925693/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j142_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v487 : ℝ := v485+v486
  have h487 : Bounds (35490015021473446248956188948289055969/2500000000000000000000000000000000000000 : ℝ) v487 (17745007510736723124478094474204337721/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h485 h486) (by norm_num) (by norm_num)
  obtain ⟨j143,hj143⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j142=z := ⟨_,rfl⟩
  have j143_value : Bounds (129660909572649424842915087961521040673/10000000000000000000000000000000000000000 : ℝ) j143.value (32415227393162356210728771990471124133/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h484
  have j143_tangent : Bounds (35490015021473446248956188948289055969/2500000000000000000000000000000000000000 : ℝ) j143.tangent (17745007510736723124478094474204337721/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj143,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h487
  let v488 : ℝ := j141.value+j143.value
  have h488 : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) v488 (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_value j143_value) (by norm_num) (by norm_num)
  let v489 : ℝ := j141.tangent+j143.tangent
  have h489 : Bounds (10293588545844473846691578349679309569131/10000000000000000000000000000000000000000 : ℝ) v489 (5146794272922236923345789174884012374751/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j141_tangent j143_tangent) (by norm_num) (by norm_num)
  obtain ⟨j144,hj144⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j141 j143=z := ⟨_,rfl⟩
  have j144_value : Bounds (2124305224415279387680426366994133154149/2500000000000000000000000000000000000000 : ℝ) j144.value (8497220897661117550721705468040105758917/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h488
  have j144_tangent : Bounds (10293588545844473846691578349679309569131/10000000000000000000000000000000000000000 : ℝ) j144.tangent (5146794272922236923345789174884012374751/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj144,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h489
  let v490 : ℝ := j135.value*j118.value
  have h490 : Bounds (95001100596627833852388053576491668151/5000000000000000000000000000000000000000 : ℝ) v490 (190002201193255667704776107154484234543/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v491 : ℝ := j135.tangent*j118.value
  have h491 : Bounds (104760591002467281610300982159359327209/5000000000000000000000000000000000000000 : ℝ) v491 (818442117206775637580476423126920979/39062500000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_tangent j118_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v492 : ℝ := j135.value*j118.tangent
  have h492 : Bounds (104760591002467281610300982159359327209/5000000000000000000000000000000000000000 : ℝ) v492 (818442117206775637580476423126920979/39062500000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j135_value j118_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v493 : ℝ := v491+v492
  have h493 : Bounds (104760591002467281610300982159359327209/2500000000000000000000000000000000000000 : ℝ) v493 (818442117206775637580476423126920979/19531250000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h491 h492) (by norm_num) (by norm_num)
  obtain ⟨j145,hj145⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j135 j118=z := ⟨_,rfl⟩
  have j145_value : Bounds (95001100596627833852388053576491668151/5000000000000000000000000000000000000000 : ℝ) j145.value (190002201193255667704776107154484234543/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h490
  have j145_tangent : Bounds (104760591002467281610300982159359327209/2500000000000000000000000000000000000000 : ℝ) j145.tangent (818442117206775637580476423126920979/19531250000000000000000000000000000000 : ℝ) := by
    simpa only [← hj145,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h493
  let v494 : ℝ := j139.value*j121.value
  have h494 : Bounds (6032569887885867449626641402127756575467/5000000000000000000000000000000000000000 : ℝ) v494 (12065139775771734899253282804268677597667/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v495 : ℝ := j139.tangent*j121.value
  have h495 : Bounds (13304595057313344764508224734283925117371/10000000000000000000000000000000000000000 : ℝ) v495 (6652297528656672382254112367152968436407/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_tangent j121_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v496 : ℝ := j139.value*j121.tangent
  have h496 : Bounds (1144454180944982031402553876451813062527/10000000000000000000000000000000000000000 : ℝ) v496 (228890836188996406280510775292024878727/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j139_value j121_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v497 : ℝ := v495+v496
  have h497 : Bounds (7224524619129163397955389305367869089949/5000000000000000000000000000000000000000 : ℝ) v497 (14449049238258326795910778610766061266449/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h495 h496) (by norm_num) (by norm_num)
  obtain ⟨j146,hj146⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j139 j121=z := ⟨_,rfl⟩
  have j146_value : Bounds (6032569887885867449626641402127756575467/5000000000000000000000000000000000000000 : ℝ) j146.value (12065139775771734899253282804268677597667/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h494
  have j146_tangent : Bounds (7224524619129163397955389305367869089949/5000000000000000000000000000000000000000 : ℝ) j146.tangent (14449049238258326795910778610766061266449/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj146,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h497
  let v498 : ℝ := j145.value+j146.value
  have h498 : Bounds (3063785494241247641739514727852124121809/2500000000000000000000000000000000000000 : ℝ) v498 (1225514197696499056695805891142316183221/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_value j146_value) (by norm_num) (by norm_num)
  let v499 : ℝ := j145.tangent+j146.tangent
  have h499 : Bounds (7434045801134097961175991269686587744367/5000000000000000000000000000000000000000 : ℝ) v499 (14868091602268195922351982539407044807697/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j145_tangent j146_tangent) (by norm_num) (by norm_num)
  obtain ⟨j147,hj147⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j145 j146=z := ⟨_,rfl⟩
  have j147_value : Bounds (3063785494241247641739514727852124121809/2500000000000000000000000000000000000000 : ℝ) j147.value (1225514197696499056695805891142316183221/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj147,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h498
  have j147_tangent : Bounds (7434045801134097961175991269686587744367/5000000000000000000000000000000000000000 : ℝ) j147.tangent (14868091602268195922351982539407044807697/10000000000000000000000000000000000000000 : ℝ) := by
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
  have h504 : Bounds (8167616351033034635774178769229671853/5000000000000000000000000000000000000000 : ℝ) v504 (8167616351033034635774178769252566711/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v505 : ℝ := j92.tangent*j148.value
  have h505 : Bounds (839061578401479652433476546632371161/5000000000000000000000000000000000000000 : ℝ) v505 (1678123156802959304866953093279593837/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_tangent j148_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v506 : ℝ := j92.value*j148.tangent
  have h506 : Bounds (32670465404132138543096715076918687413/10000000000000000000000000000000000000000 : ℝ) v506 (32670465404132138543096715077010266843/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j92_value j148_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v507 : ℝ := v505+v506
  have h507 : Bounds (6869717712187019569592733634036685947/2000000000000000000000000000000000000000 : ℝ) v507 (858714714023377446199091704257246517/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h505 h506) (by norm_num) (by norm_num)
  obtain ⟨j149,hj149⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j92 j148=z := ⟨_,rfl⟩
  have j149_value : Bounds (8167616351033034635774178769229671853/5000000000000000000000000000000000000000 : ℝ) j149.value (8167616351033034635774178769252566711/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h504
  have j149_tangent : Bounds (6869717712187019569592733634036685947/2000000000000000000000000000000000000000 : ℝ) j149.tangent (858714714023377446199091704257246517/250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj149,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h507
  let v508 : ℝ := j147.value+j149.value
  have h508 : Bounds (6135738604833528318114803634473477915471/5000000000000000000000000000000000000000 : ℝ) v508 (95870915700523879970543806788763023169/78125000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_value j149_value) (by norm_num) (by norm_num)
  let v509 : ℝ := j147.tangent+j149.tangent
  have h509 : Bounds (14902440190829131020199946207543358918469/10000000000000000000000000000000000000000 : ℝ) v509 (14902440190829131020199946207577334668377/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j147_tangent j149_tangent) (by norm_num) (by norm_num)
  obtain ⟨j150,hj150⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j147 j149=z := ⟨_,rfl⟩
  have j150_value : Bounds (6135738604833528318114803634473477915471/5000000000000000000000000000000000000000 : ℝ) j150.value (95870915700523879970543806788763023169/78125000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h508
  have j150_tangent : Bounds (14902440190829131020199946207543358918469/10000000000000000000000000000000000000000 : ℝ) j150.tangent (14902440190829131020199946207577334668377/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj150,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h509
  have hm12 : jetIter c d 1 2=!![j115,j126;j144,j150] := by
    rw [jetIter,hm11]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj79,← hj80,← hj81,← hj82,← hj83,← hj84,← hj85,← hj86,← hj87,← hj88,← hj89,← hj90,← hj91,← hj92,← hj93,← hj94,← hj95,← hj96,← hj97,← hj98,← hj99,← hj100,← hj101,← hj102,← hj103,← hj104,← hj105,← hj106,← hj107,← hj108,← hj109,← hj110,← hj111,← hj112,← hj113,← hj114,← hj115,← hj116,← hj117,← hj118,← hj119,← hj120,← hj121,← hj122,← hj123,← hj124,← hj125,← hj126,← hj127,← hj128,← hj129,← hj130,← hj131,← hj132,← hj133,← hj134,← hj135,← hj136,← hj137,← hj138,← hj139,← hj140,← hj141,← hj142,← hj143,← hj144,← hj145,← hj146,← hj147,← hj148,← hj149,← hj150]
    all_goals rfl
  let v510 : ℝ := -c
  have h510 : Bounds (-39810178453389828830806414063/125000000000000000000000000000 : ℝ) v510 (-318481427627118630646451312501/1000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hc) (by norm_num) (by norm_num)
  let v511 : ℝ := (1 : ℝ)+v510
  have h511 : Bounds (85189821546610171169193585937/125000000000000000000000000000 : ℝ) v511 (681518572372881369353548687499/1000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (1 : ℝ)) h510) (by norm_num) (by norm_num)
  obtain ⟨j151,hj151⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((1 : ℝ)+(-c))=z := ⟨_,rfl⟩
  have j151_value : Bounds (85189821546610171169193585937/125000000000000000000000000000 : ℝ) j151.value (681518572372881369353548687499/1000000000000000000000000000000 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h511
  have j151_tangent : Bounds (0 : ℝ) j151.tangent (0 : ℝ) := by
    simpa only [← hj151,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j152,hj152⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant (-1/16 : ℝ)=z := ⟨_,rfl⟩
  have j152_value : Bounds (-1/16 : ℝ) j152.value (-1/16 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (-1/16 : ℝ))
  have j152_tangent : Bounds (0 : ℝ) j152.tangent (0 : ℝ) := by
    simpa only [← hj152,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  obtain ⟨j153,hj153⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant c=z := ⟨_,rfl⟩
  have j153_value : Bounds (318481427627118630646451312501/1000000000000000000000000000000 : ℝ) j153.value (39810178453389828830806414063/125000000000000000000000000000 : ℝ) := by
    convert hc using 1 <;> norm_num [← hj153,LReturnJets.constant]
  have j153_tangent : Bounds (0 : ℝ) j153.tangent (0 : ℝ) := by
    simpa only [← hj153,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v512 : ℝ := j115.value*j153.value
  have h512 : Bounds (134207716972445318316609173398817372079/625000000000000000000000000000000000000 : ℝ) v512 (53683086788978127326643669360688418041/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v513 : ℝ := j115.tangent*j153.value
  have h513 : Bounds (2236008659506924935733700914747288685313/10000000000000000000000000000000000000000 : ℝ) v513 (2236008659506924935733700914802009641547/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v514 : ℝ := j115.value*j153.tangent
  have h514 : Bounds (0 : ℝ) v514 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j115_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v515 : ℝ := v513+v514
  have h515 : Bounds (2236008659506924935733700914747288685313/10000000000000000000000000000000000000000 : ℝ) v515 (2236008659506924935733700914802009641547/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h513 h514) (by norm_num) (by norm_num)
  obtain ⟨j154,hj154⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j115 j153=z := ⟨_,rfl⟩
  have j154_value : Bounds (134207716972445318316609173398817372079/625000000000000000000000000000000000000 : ℝ) j154.value (53683086788978127326643669360688418041/250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h512
  have j154_tangent : Bounds (2236008659506924935733700914747288685313/10000000000000000000000000000000000000000 : ℝ) j154.tangent (2236008659506924935733700914802009641547/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj154,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h515
  obtain ⟨j155,hj155⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant d=z := ⟨_,rfl⟩
  have j155_value : Bounds (-205046423935149745096270174003/200000000000000000000000000000 : ℝ) j155.value (-256308029918937181370337717503/250000000000000000000000000000 : ℝ) := by
    convert hd using 1 <;> norm_num [← hj155,LReturnJets.constant]
  have j155_tangent : Bounds (0 : ℝ) j155.tangent (0 : ℝ) := by
    simpa only [← hj155,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v516 : ℝ := j126.value*j155.value
  have h516 : Bounds (-871162379226217588216250441506677791573/1000000000000000000000000000000000000000 : ℝ) v516 (-435581189613108794108125220748805451279/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v517 : ℝ := j126.tangent*j155.value
  have h517 : Bounds (-659582350245383619172970191456471931841/625000000000000000000000000000000000000 : ℝ) v517 (-10553317603926137906767523063181716491397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j126_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v518 : ℝ := j126.value*j155.tangent
  have h518 : Bounds (0 : ℝ) v518 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j126_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v519 : ℝ := v517+v518
  have h519 : Bounds (-659582350245383619172970191456471931841/625000000000000000000000000000000000000 : ℝ) v519 (-10553317603926137906767523063181716491397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h517 h518) (by norm_num) (by norm_num)
  obtain ⟨j156,hj156⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j126 j155=z := ⟨_,rfl⟩
  have j156_value : Bounds (-871162379226217588216250441506677791573/1000000000000000000000000000000000000000 : ℝ) j156.value (-435581189613108794108125220748805451279/500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h516
  have j156_tangent : Bounds (-659582350245383619172970191456471931841/625000000000000000000000000000000000000 : ℝ) j156.tangent (-10553317603926137906767523063181716491397/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj156,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h519
  let v520 : ℝ := j154.value+j156.value
  have h520 : Bounds (-3282150160351525394548378820342849981233/5000000000000000000000000000000000000000 : ℝ) v520 (-328215016035152539454837882027428615197/500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_value j156_value) (by norm_num) (by norm_num)
  let v521 : ℝ := j154.tangent+j156.tangent
  have h521 : Bounds (-8317308944419212971033822148556262224143/10000000000000000000000000000000000000000 : ℝ) v521 (-166346178888384259420676442967594136997/200000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j154_tangent j156_tangent) (by norm_num) (by norm_num)
  obtain ⟨j157,hj157⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j154 j156=z := ⟨_,rfl⟩
  have j157_value : Bounds (-3282150160351525394548378820342849981233/5000000000000000000000000000000000000000 : ℝ) j157.value (-328215016035152539454837882027428615197/500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h520
  have j157_tangent : Bounds (-8317308944419212971033822148556262224143/10000000000000000000000000000000000000000 : ℝ) j157.tangent (-166346178888384259420676442967594136997/200000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj157,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h521
  let v522 : ℝ := j152.value*j157.value
  have h522 : Bounds (102567192510985168579636838133571442249/2500000000000000000000000000000000000000 : ℝ) v522 (82053754008788134863709470508571249531/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v523 : ℝ := j152.tangent*j157.value
  have h523 : Bounds (0 : ℝ) v523 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j157_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v524 : ℝ := j152.value*j157.tangent
  have h524 : Bounds (103966361805240162137922776854746335623/2000000000000000000000000000000000000000 : ℝ) v524 (519831809026200810689613884284766389009/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j157_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v525 : ℝ := v523+v524
  have h525 : Bounds (103966361805240162137922776854746335623/2000000000000000000000000000000000000000 : ℝ) v525 (519831809026200810689613884284766389009/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h523 h524) (by norm_num) (by norm_num)
  obtain ⟨j158,hj158⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j157=z := ⟨_,rfl⟩
  have j158_value : Bounds (102567192510985168579636838133571442249/2500000000000000000000000000000000000000 : ℝ) j158.value (82053754008788134863709470508571249531/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h522
  have j158_tangent : Bounds (103966361805240162137922776854746335623/2000000000000000000000000000000000000000 : ℝ) j158.tangent (519831809026200810689613884284766389009/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj158,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h525
  let v526 : ℝ := j151.value*j158.value
  have h526 : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) v526 (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v527 : ℝ := j151.tangent*j158.value
  have h527 : Bounds (0 : ℝ) v527 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v528 : ℝ := j151.value*j158.tangent
  have h528 : Bounds (88568758090387170967412539650086138031/2500000000000000000000000000000000000000 : ℝ) v528 (354275032361548683869650158609424407967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v529 : ℝ := v527+v528
  have h529 : Bounds (88568758090387170967412539650086138031/2500000000000000000000000000000000000000 : ℝ) v529 (354275032361548683869650158609424407967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h527 h528) (by norm_num) (by norm_num)
  obtain ⟨j159,hj159⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j158=z := ⟨_,rfl⟩
  have j159_value : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) j159.value (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h526
  have j159_tangent : Bounds (88568758090387170967412539650086138031/2500000000000000000000000000000000000000 : ℝ) j159.tangent (354275032361548683869650158609424407967/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj159,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h529
  let v530 : ℝ := -d
  have h530 : Bounds (256308029918937181370337717503/250000000000000000000000000000 : ℝ) v530 (205046423935149745096270174003/200000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg hd) (by norm_num) (by norm_num)
  let v531 : ℝ := (0 : ℝ)+v530
  have h531 : Bounds (256308029918937181370337717503/250000000000000000000000000000 : ℝ) v531 (205046423935149745096270174003/200000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add (IntervalBounds.exact (0 : ℝ)) h530) (by norm_num) (by norm_num)
  obtain ⟨j160,hj160⟩ : ∃ z : LReturnJets.Jet, LReturnJets.constant ((0 : ℝ)+(-d))=z := ⟨_,rfl⟩
  have j160_value : Bounds (256308029918937181370337717503/250000000000000000000000000000 : ℝ) j160.value (205046423935149745096270174003/200000000000000000000000000000 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h531
  have j160_tangent : Bounds (0 : ℝ) j160.tangent (0 : ℝ) := by
    simpa only [← hj160,LReturnJets.constant,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using (IntervalBounds.exact (0 : ℝ))
  let v532 : ℝ := j144.value*j153.value
  have h532 : Bounds (676551760587524803402560870474093799091/2500000000000000000000000000000000000000 : ℝ) v532 (338275880293762401701280435242764215523/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v533 : ℝ := j144.tangent*j153.value
  have h533 : Bounds (3278316775486704104066495559302644278751/10000000000000000000000000000000000000000 : ℝ) v533 (1639158387743352052033247779680889590843/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_tangent j153_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v534 : ℝ := j144.value*j153.tangent
  have h534 : Bounds (0 : ℝ) v534 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j144_value j153_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v535 : ℝ := v533+v534
  have h535 : Bounds (3278316775486704104066495559302644278751/10000000000000000000000000000000000000000 : ℝ) v535 (1639158387743352052033247779680889590843/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h533 h534) (by norm_num) (by norm_num)
  obtain ⟨j161,hj161⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j144 j153=z := ⟨_,rfl⟩
  have j161_value : Bounds (676551760587524803402560870474093799091/2500000000000000000000000000000000000000 : ℝ) j161.value (338275880293762401701280435242764215523/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h532
  have j161_tangent : Bounds (3278316775486704104066495559302644278751/10000000000000000000000000000000000000000 : ℝ) j161.tangent (1639158387743352052033247779680889590843/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj161,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h535
  let v536 : ℝ := j150.value*j155.value
  have h536 : Bounds (-12581112591219598843860649858572800952533/10000000000000000000000000000000000000000 : ℝ) v536 (-6290556295609799421930324929260452096551/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_value j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v537 : ℝ := j150.tangent*j155.value
  have h537 : Bounds (-15278460345184819328283067185040692414051/10000000000000000000000000000000000000000 : ℝ) v537 (-7639230172592409664141533592480576031691/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j150_tangent j155_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v538 : ℝ := j150.value*j155.tangent
  have h538 : Bounds (0 : ℝ) v538 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j150_value j155_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v539 : ℝ := v537+v538
  have h539 : Bounds (-15278460345184819328283067185040692414051/10000000000000000000000000000000000000000 : ℝ) v539 (-7639230172592409664141533592480576031691/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h537 h538) (by norm_num) (by norm_num)
  obtain ⟨j162,hj162⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j150 j155=z := ⟨_,rfl⟩
  have j162_value : Bounds (-12581112591219598843860649858572800952533/10000000000000000000000000000000000000000 : ℝ) j162.value (-6290556295609799421930324929260452096551/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h536
  have j162_tangent : Bounds (-15278460345184819328283067185040692414051/10000000000000000000000000000000000000000 : ℝ) j162.tangent (-7639230172592409664141533592480576031691/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj162,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h539
  let v540 : ℝ := j161.value+j162.value
  have h540 : Bounds (-9874905548869499630250406376676425756169/10000000000000000000000000000000000000000 : ℝ) v540 (-4937452774434749815125203188289395234459/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_value j162_value) (by norm_num) (by norm_num)
  let v541 : ℝ := j161.tangent+j162.tangent
  have h541 : Bounds (-120001435696981152242165716257380481353/100000000000000000000000000000000000000 : ℝ) v541 (-375004486553066100756767863299980402553/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j161_tangent j162_tangent) (by norm_num) (by norm_num)
  obtain ⟨j163,hj163⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j161 j162=z := ⟨_,rfl⟩
  have j163_value : Bounds (-9874905548869499630250406376676425756169/10000000000000000000000000000000000000000 : ℝ) j163.value (-4937452774434749815125203188289395234459/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h540
  have j163_tangent : Bounds (-120001435696981152242165716257380481353/100000000000000000000000000000000000000 : ℝ) j163.tangent (-375004486553066100756767863299980402553/312500000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj163,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h541
  let v542 : ℝ := j152.value*j163.value
  have h542 : Bounds (617181596804343726890650398536174404307/10000000000000000000000000000000000000000 : ℝ) v542 (617181596804343726890650398542276609761/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v543 : ℝ := j152.tangent*j163.value
  have h543 : Bounds (0 : ℝ) v543 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j152_tangent j163_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v544 : ℝ := j152.value*j163.tangent
  have h544 : Bounds (375004486553066100756767863299980402553/5000000000000000000000000000000000000000 : ℝ) v544 (750008973106132201513535726608628008457/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j152_value j163_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v545 : ℝ := v543+v544
  have h545 : Bounds (375004486553066100756767863299980402553/5000000000000000000000000000000000000000 : ℝ) v545 (750008973106132201513535726608628008457/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h543 h544) (by norm_num) (by norm_num)
  obtain ⟨j164,hj164⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j152 j163=z := ⟨_,rfl⟩
  have j164_value : Bounds (617181596804343726890650398536174404307/10000000000000000000000000000000000000000 : ℝ) j164.value (617181596804343726890650398542276609761/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h542
  have j164_tangent : Bounds (375004486553066100756767863299980402553/5000000000000000000000000000000000000000 : ℝ) j164.tangent (750008973106132201513535726608628008457/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj164,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h545
  let v546 : ℝ := j160.value*j164.value
  have h546 : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) v546 (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v547 : ℝ := j160.tangent*j164.value
  have h547 : Bounds (0 : ℝ) v547 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v548 : ℝ := j160.value*j164.tangent
  have h548 : Bounds (384466644636715768263951418369970382119/5000000000000000000000000000000000000000 : ℝ) v548 (768933289273431536527902836751076686421/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v549 : ℝ := v547+v548
  have h549 : Bounds (384466644636715768263951418369970382119/5000000000000000000000000000000000000000 : ℝ) v549 (768933289273431536527902836751076686421/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h547 h548) (by norm_num) (by norm_num)
  obtain ⟨j165,hj165⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j164=z := ⟨_,rfl⟩
  have j165_value : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) j165.value (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h546
  have j165_tangent : Bounds (384466644636715768263951418369970382119/5000000000000000000000000000000000000000 : ℝ) j165.tangent (768933289273431536527902836751076686421/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj165,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h549
  let v550 : ℝ := j159.value+j165.value
  have h550 : Bounds (36494407326644201253872530985702864827/400000000000000000000000000000000000000 : ℝ) v550 (91236018316610503134681327465775108919/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_value j165_value) (by norm_num) (by norm_num)
  let v551 : ℝ := j159.tangent+j165.tangent
  have h551 : Bounds (561604160817490110198776497670142658181/5000000000000000000000000000000000000000 : ℝ) v551 (280802080408745055099388248840125273597/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j159_tangent j165_tangent) (by norm_num) (by norm_num)
  obtain ⟨j166,hj166⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j159 j165=z := ⟨_,rfl⟩
  have j166_value : Bounds (36494407326644201253872530985702864827/400000000000000000000000000000000000000 : ℝ) j166.value (91236018316610503134681327465775108919/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h550
  have j166_tangent : Bounds (561604160817490110198776497670142658181/5000000000000000000000000000000000000000 : ℝ) j166.tangent (280802080408745055099388248840125273597/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj166,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h551
  let v552 : ℝ := j166.value⁻¹
  have h552 : Bounds (54802917666231560702768831396561850923989/5000000000000000000000000000000000000000 : ℝ) v552 (109605835332463121405537662794947278059641/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j166_value (by norm_num)) (by norm_num) (by norm_num)
  let v553 : ℝ := -j166.tangent
  have h553 : Bounds (-280802080408745055099388248840125273597/2500000000000000000000000000000000000000 : ℝ) v553 (-561604160817490110198776497670142658181/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j166_tangent) (by norm_num) (by norm_num)
  let v554 : ℝ := j166.value*j166.value
  have h554 : Bounds (16648022076537774452423789457563552549/2000000000000000000000000000000000000000 : ℝ) v554 (83240110382688872262118947290587591281/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j166_value j166_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v555 : ℝ := v554⁻¹
  have h555 : Bounds (150167989236587764590654817543634830918689/1250000000000000000000000000000000000000 : ℝ) v555 (120134391389270211672523854038905356615911/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h554 (by norm_num)) (by norm_num) (by norm_num)
  let v556 : ℝ := v553*v555
  have h556 : Bounds (-269871896245964028379389623434737764319/20000000000000000000000000000000000000 : ℝ) v556 (-134935948122982014189694811710450255823523/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn h553 h555 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j167,hj167⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j166=z := ⟨_,rfl⟩
  have j167_value : Bounds (54802917666231560702768831396561850923989/5000000000000000000000000000000000000000 : ℝ) j167.value (109605835332463121405537662794947278059641/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h552
  have j167_tangent : Bounds (-269871896245964028379389623434737764319/20000000000000000000000000000000000000 : ℝ) j167.tangent (-134935948122982014189694811710450255823523/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj167,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h556
  let v557 : ℝ := j158.value*j151.value
  have h557 : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) v557 (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v558 : ℝ := j158.tangent*j151.value
  have h558 : Bounds (88568758090387170967412539650086138031/2500000000000000000000000000000000000000 : ℝ) v558 (354275032361548683869650158609424407967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v559 : ℝ := j158.value*j151.tangent
  have h559 : Bounds (0 : ℝ) v559 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v560 : ℝ := v558+v559
  have h560 : Bounds (88568758090387170967412539650086138031/2500000000000000000000000000000000000000 : ℝ) v560 (354275032361548683869650158609424407967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h558 h559) (by norm_num) (by norm_num)
  obtain ⟨j168,hj168⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j151=z := ⟨_,rfl⟩
  have j168_value : Bounds (279605786449524406391274238777863564883/10000000000000000000000000000000000000000 : ℝ) j168.value (139802893224762203195637119392467655787/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h557
  have j168_tangent : Bounds (88568758090387170967412539650086138031/2500000000000000000000000000000000000000 : ℝ) j168.tangent (354275032361548683869650158609424407967/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj168,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h560
  let v561 : ℝ := j167.value*j168.value
  have h561 : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) v561 (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v562 : ℝ := j167.tangent*j168.value
  have h562 : Bounds (-3772887189523861272220003619420637607891/10000000000000000000000000000000000000000 : ℝ) v562 (-943221797380965318055000904782941381911/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j168_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v563 : ℝ := j167.value*j168.tangent
  have h563 : Bounds (485382635742786856045654765423502024053/1250000000000000000000000000000000000000 : ℝ) v563 (1941530542971147424182619061776070731501/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j168_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v564 : ℝ := v562+v563
  have h564 : Bounds (110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) v564 (55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h562 h563) (by norm_num) (by norm_num)
  obtain ⟨j169,hj169⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j168=z := ⟨_,rfl⟩
  have j169_value : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) j169.value (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h561
  have j169_tangent : Bounds (110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) j169.tangent (55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj169,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h564
  let v565 : ℝ := -j169.value
  have h565 : Bounds (-3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) v565 (-47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_value) (by norm_num) (by norm_num)
  let v566 : ℝ := j0.value+v565
  have h566 : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) v566 (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h565) (by norm_num) (by norm_num)
  let v567 : ℝ := -j169.tangent
  have h567 : Bounds (-55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) v567 (-110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j169_tangent) (by norm_num) (by norm_num)
  let v568 : ℝ := j0.tangent+v567
  have h568 : Bounds (-55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) v568 (-110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h567) (by norm_num) (by norm_num)
  obtain ⟨j170,hj170⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j169=z := ⟨_,rfl⟩
  have j170_value : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) j170.value (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h566
  have j170_tangent : Bounds (-55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) j170.tangent (-110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj170,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h568
  let v569 : ℝ := j170.value*j115.value
  have h569 : Bounds (4676082961961197156336293331224428345527/10000000000000000000000000000000000000000 : ℝ) v569 (935216592392239431267258666273637988411/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v570 : ℝ := j170.tangent*j115.value
  have h570 : Bounds (-2971338021122103141682330348119091167/400000000000000000000000000000000000000 : ℝ) v570 (-72542432156301346232478767965470423/9765625000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v571 : ℝ := j170.value*j115.tangent
  have h571 : Bounds (4869206774853685668769617147271510345093/10000000000000000000000000000000000000000 : ℝ) v571 (973841354970737133753923429487004599473/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v572 : ℝ := v570+v571
  have h572 : Bounds (2397461662162816545113779444284266532959/5000000000000000000000000000000000000000 : ℝ) v572 (4794923324325633090227558889038381284213/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h570 h571) (by norm_num) (by norm_num)
  obtain ⟨j171,hj171⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j115=z := ⟨_,rfl⟩
  have j171_value : Bounds (4676082961961197156336293331224428345527/10000000000000000000000000000000000000000 : ℝ) j171.value (935216592392239431267258666273637988411/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h569
  have j171_tangent : Bounds (2397461662162816545113779444284266532959/5000000000000000000000000000000000000000 : ℝ) j171.tangent (4794923324325633090227558889038381284213/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj171,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h572
  let v573 : ℝ := j158.value*j160.value
  have h573 : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) v573 (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v574 : ℝ := j158.tangent*j160.value
  have h574 : Bounds (1665463335758783956490471490056016413/31250000000000000000000000000000000000 : ℝ) v574 (532948267442810866076950876830797887627/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v575 : ℝ := j158.value*j160.tangent
  have h575 : Bounds (0 : ℝ) v575 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v576 : ℝ := v574+v575
  have h576 : Bounds (1665463335758783956490471490056016413/31250000000000000000000000000000000000 : ℝ) v576 (532948267442810866076950876830797887627/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h574 h575) (by norm_num) (by norm_num)
  obtain ⟨j172,hj172⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j160=z := ⟨_,rfl⟩
  have j172_value : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) j172.value (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h573
  have j172_tangent : Bounds (1665463335758783956490471490056016413/31250000000000000000000000000000000000 : ℝ) j172.tangent (532948267442810866076950876830797887627/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj172,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h576
  let v577 : ℝ := j167.value*j172.value
  have h577 : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) v577 (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v578 : ℝ := j167.tangent*j172.value
  have h578 : Bounds (-5675685575442644273962028028403998556197/10000000000000000000000000000000000000000 : ℝ) v578 (-709460696930330534245253503497226777571/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j172_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v579 : ℝ := j167.value*j172.tangent
  have h579 : Bounds (584142400420582442651475594246690950059/1000000000000000000000000000000000000000 : ℝ) v579 (730178000525728053314344492838148534397/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j172_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v580 : ℝ := v578+v579
  have h580 : Bounds (165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) v580 (10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h578 h579) (by norm_num) (by norm_num)
  obtain ⟨j173,hj173⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j172=z := ⟨_,rfl⟩
  have j173_value : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) j173.value (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h577
  have j173_tangent : Bounds (165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) j173.tangent (10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj173,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h580
  let v581 : ℝ := -j173.value
  have h581 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v581 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_value) (by norm_num) (by norm_num)
  let v582 : ℝ := j6.value+v581
  have h582 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v582 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h581) (by norm_num) (by norm_num)
  let v583 : ℝ := -j173.tangent
  have h583 : Bounds (-10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) v583 (-165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j173_tangent) (by norm_num) (by norm_num)
  let v584 : ℝ := j6.tangent+v583
  have h584 : Bounds (-10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) v584 (-165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h583) (by norm_num) (by norm_num)
  obtain ⟨j174,hj174⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j173=z := ⟨_,rfl⟩
  have j174_value : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) j174.value (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h582
  have j174_tangent : Bounds (-10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) j174.tangent (-165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj174,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h584
  let v585 : ℝ := j174.value*j144.value
  have h585 : Bounds (-783486005698744571990616749549511801631/2000000000000000000000000000000000000000 : ℝ) v585 (-1958715014246861429976541873779887909077/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v586 : ℝ := j174.tangent*j144.value
  have h586 : Bounds (-140831604043201284053106505434372525819/10000000000000000000000000000000000000000 : ℝ) v586 (-70415802021600642026553252434354945981/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v587 : ℝ := j174.value*j144.tangent
  have h587 : Bounds (-4745600162230639122452184894669854821029/10000000000000000000000000000000000000000 : ℝ) v587 (-1186400040557659780613046223609244502927/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v588 : ℝ := v586+v587
  have h588 : Bounds (-152700992696057512703290356253257104589/312500000000000000000000000000000000000 : ℝ) v588 (-488643176627384040650529139930568790367/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h586 h587) (by norm_num) (by norm_num)
  obtain ⟨j175,hj175⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j144=z := ⟨_,rfl⟩
  have j175_value : Bounds (-783486005698744571990616749549511801631/2000000000000000000000000000000000000000 : ℝ) j175.value (-1958715014246861429976541873779887909077/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h585
  have j175_tangent : Bounds (-152700992696057512703290356253257104589/312500000000000000000000000000000000000 : ℝ) j175.tangent (-488643176627384040650529139930568790367/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj175,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h588
  let v589 : ℝ := j171.value+j175.value
  have h589 : Bounds (189663233366868574095802395869217334343/2500000000000000000000000000000000000000 : ℝ) v589 (758652933467474296383209583808414123901/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_value j175_value) (by norm_num) (by norm_num)
  let v590 : ℝ := j171.tangent+j175.tangent
  have h590 : Bounds (-9150844194820731627773251153569428093/1000000000000000000000000000000000000000 : ℝ) v590 (-91508441948207316277732510267306619457/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j171_tangent j175_tangent) (by norm_num) (by norm_num)
  obtain ⟨j176,hj176⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j171 j175=z := ⟨_,rfl⟩
  have j176_value : Bounds (189663233366868574095802395869217334343/2500000000000000000000000000000000000000 : ℝ) j176.value (758652933467474296383209583808414123901/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h589
  have j176_tangent : Bounds (-9150844194820731627773251153569428093/1000000000000000000000000000000000000000 : ℝ) j176.tangent (-91508441948207316277732510267306619457/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj176,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h590
  let v591 : ℝ := j167.value*j159.value
  have h591 : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) v591 (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v592 : ℝ := j167.tangent*j159.value
  have h592 : Bounds (-3772887189523861272220003619420637607891/10000000000000000000000000000000000000000 : ℝ) v592 (-943221797380965318055000904782941381911/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j159_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v593 : ℝ := j167.value*j159.tangent
  have h593 : Bounds (485382635742786856045654765423502024053/1250000000000000000000000000000000000000 : ℝ) v593 (1941530542971147424182619061776070731501/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j159_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v594 : ℝ := v592+v593
  have h594 : Bounds (110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) v594 (55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h592 h593) (by norm_num) (by norm_num)
  obtain ⟨j177,hj177⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j159=z := ⟨_,rfl⟩
  have j177_value : Bounds (47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) j177.value (3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h591
  have j177_tangent : Bounds (110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) j177.tangent (55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj177,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h594
  let v595 : ℝ := -j177.value
  have h595 : Bounds (-3064642578759042044145401991121086848703/10000000000000000000000000000000000000000 : ℝ) v595 (-47885040293110031939771906109259189567/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_value) (by norm_num) (by norm_num)
  let v596 : ℝ := j0.value+v595
  have h596 : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) v596 (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h595) (by norm_num) (by norm_num)
  let v597 : ℝ := -j177.tangent
  have h597 : Bounds (-55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) v597 (-110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j177_tangent) (by norm_num) (by norm_num)
  let v598 : ℝ := j0.tangent+v597
  have h598 : Bounds (-55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) v598 (-110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h597) (by norm_num) (by norm_num)
  obtain ⟨j178,hj178⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j177=z := ⟨_,rfl⟩
  have j178_value : Bounds (6935357421240957955854598008878913151297/10000000000000000000000000000000000000000 : ℝ) j178.value (108364959706889968060228093890740810433/156250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h596
  have j178_tangent : Bounds (-55086948209216788072617252210187967679/5000000000000000000000000000000000000000 : ℝ) j178.tangent (-110173896418433576145234503967378584533/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj178,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h598
  let v599 : ℝ := j176.value*j178.value
  have h599 : Bounds (526152925226987058359946299640763692533/10000000000000000000000000000000000000000 : ℝ) v599 (263076462613493529179973149940225222461/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v600 : ℝ := j176.tangent*j178.value
  have h600 : Bounds (-63464375197169699570854545407467437773/10000000000000000000000000000000000000000 : ℝ) v600 (-31732187598584849785427272263309693969/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j176_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v601 : ℝ := j176.value*j178.tangent
  have h601 : Bounds (-8358374970938629251626484117563482021/10000000000000000000000000000000000000000 : ℝ) v601 (-4179187485469314625813242039771973509/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v602 : ℝ := v600+v601
  have h602 : Bounds (-35911375084054164411240514762515459897/5000000000000000000000000000000000000000 : ℝ) v602 (-17955687542027082205620257151540833739/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h600 h601) (by norm_num) (by norm_num)
  obtain ⟨j179,hj179⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j178=z := ⟨_,rfl⟩
  have j179_value : Bounds (526152925226987058359946299640763692533/10000000000000000000000000000000000000000 : ℝ) j179.value (263076462613493529179973149940225222461/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h599
  have j179_tangent : Bounds (-35911375084054164411240514762515459897/5000000000000000000000000000000000000000 : ℝ) j179.tangent (-17955687542027082205620257151540833739/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj179,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h602
  let v603 : ℝ := j170.value*j126.value
  have h603 : Bounds (1473281600312944653162412978782232909359/2500000000000000000000000000000000000000 : ℝ) v603 (147328160031294465316241297882055252043/250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v604 : ℝ := j170.tangent*j126.value
  have h604 : Bounds (-93617193502346513578134902210560088589/10000000000000000000000000000000000000000 : ℝ) v604 (-93617193502346513578134901824937822907/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j170_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v605 : ℝ := j170.value*j126.tangent
  have h605 : Bounds (3569485785631169622945392132364929659973/5000000000000000000000000000000000000000 : ℝ) v605 (1784742892815584811472696066230914439987/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j170_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v606 : ℝ := v604+v605
  have h606 : Bounds (7045354377759992732312649362519299231357/10000000000000000000000000000000000000000 : ℝ) v606 (7045354377759992732312649363098719937041/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h604 h605) (by norm_num) (by norm_num)
  obtain ⟨j180,hj180⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j170 j126=z := ⟨_,rfl⟩
  have j180_value : Bounds (1473281600312944653162412978782232909359/2500000000000000000000000000000000000000 : ℝ) j180.value (147328160031294465316241297882055252043/250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h603
  have j180_tangent : Bounds (7045354377759992732312649362519299231357/10000000000000000000000000000000000000000 : ℝ) j180.tangent (7045354377759992732312649363098719937041/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj180,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h606
  let v607 : ℝ := j174.value*j150.value
  have h607 : Bounds (-5657455995801899525654765889147437808099/10000000000000000000000000000000000000000 : ℝ) v607 (-1414363998950474881413691472227947698813/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v608 : ℝ := j174.tangent*j150.value
  have h608 : Bounds (-101692767566669610959834555878458362033/5000000000000000000000000000000000000000 : ℝ) v608 (-25423191891667402739958638867659814083/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v609 : ℝ := j174.value*j150.tangent
  have h609 : Bounds (-137407906430806831217316926539000680719/200000000000000000000000000000000000000 : ℝ) v609 (-3435197660770170780432923163328218859423/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j174_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v610 : ℝ := v608+v609
  have h610 : Bounds (-442111303542105048924094714919184422501/625000000000000000000000000000000000000 : ℝ) v610 (-707378085667368078278551543759771623151/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h608 h609) (by norm_num) (by norm_num)
  obtain ⟨j181,hj181⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j174 j150=z := ⟨_,rfl⟩
  have j181_value : Bounds (-5657455995801899525654765889147437808099/10000000000000000000000000000000000000000 : ℝ) j181.value (-1414363998950474881413691472227947698813/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h607
  have j181_tangent : Bounds (-442111303542105048924094714919184422501/625000000000000000000000000000000000000 : ℝ) j181.tangent (-707378085667368078278551543759771623151/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj181,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h610
  let v611 : ℝ := j180.value+j181.value
  have h611 : Bounds (235670405449879086994886025981493829337/10000000000000000000000000000000000000000 : ℝ) v611 (58917601362469771748721506592604821617/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_value j181_value) (by norm_num) (by norm_num)
  let v612 : ℝ := j180.tangent+j181.tangent
  have h612 : Bounds (-28426478913688050472866076187651528659/10000000000000000000000000000000000000000 : ℝ) v612 (-28426478913688050472866074498996294469/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j180_tangent j181_tangent) (by norm_num) (by norm_num)
  obtain ⟨j182,hj182⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j180 j181=z := ⟨_,rfl⟩
  have j182_value : Bounds (235670405449879086994886025981493829337/10000000000000000000000000000000000000000 : ℝ) j182.value (58917601362469771748721506592604821617/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h611
  have j182_tangent : Bounds (-28426478913688050472866076187651528659/10000000000000000000000000000000000000000 : ℝ) j182.tangent (-28426478913688050472866074498996294469/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj182,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h612
  let v613 : ℝ := j160.value*j158.value
  have h613 : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) v613 (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v614 : ℝ := j160.tangent*j158.value
  have h614 : Bounds (0 : ℝ) v614 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v615 : ℝ := j160.value*j158.tangent
  have h615 : Bounds (1665463335758783956490471490056016413/31250000000000000000000000000000000000 : ℝ) v615 (532948267442810866076950876830797887627/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j160_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v616 : ℝ := v614+v615
  have h616 : Bounds (1665463335758783956490471490056016413/31250000000000000000000000000000000000 : ℝ) v616 (532948267442810866076950876830797887627/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h614 h615) (by norm_num) (by norm_num)
  obtain ⟨j183,hj183⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j160 j158=z := ⟨_,rfl⟩
  have j183_value : Bounds (210310360374455809551943758643184221739/5000000000000000000000000000000000000000 : ℝ) j183.value (420620720748911619103887517296385979791/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h613
  have j183_tangent : Bounds (1665463335758783956490471490056016413/31250000000000000000000000000000000000 : ℝ) j183.tangent (532948267442810866076950876830797887627/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj183,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h616
  let v617 : ℝ := j167.value*j183.value
  have h617 : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) v617 (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v618 : ℝ := j167.tangent*j183.value
  have h618 : Bounds (-5675685575442644273962028028403998556197/10000000000000000000000000000000000000000 : ℝ) v618 (-709460696930330534245253503497226777571/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j183_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v619 : ℝ := j167.value*j183.tangent
  have h619 : Bounds (584142400420582442651475594246690950059/1000000000000000000000000000000000000000 : ℝ) v619 (730178000525728053314344492838148534397/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j183_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v620 : ℝ := v618+v619
  have h620 : Bounds (165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) v620 (10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h618 h619) (by norm_num) (by norm_num)
  obtain ⟨j184,hj184⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j183=z := ⟨_,rfl⟩
  have j184_value : Bounds (4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) j184.value (922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h617
  have j184_tangent : Bounds (165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) j184.tangent (10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj184,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h620
  let v621 : ℝ := -j184.value
  have h621 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v621 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_value) (by norm_num) (by norm_num)
  let v622 : ℝ := j6.value+v621
  have h622 : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) v622 (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h621) (by norm_num) (by norm_num)
  let v623 : ℝ := -j184.tangent
  have h623 : Bounds (-10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) v623 (-165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j184_tangent) (by norm_num) (by norm_num)
  let v624 : ℝ := j6.tangent+v623
  have h624 : Bounds (-10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) v624 (-165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h623) (by norm_num) (by norm_num)
  obtain ⟨j185,hj185⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j184=z := ⟨_,rfl⟩
  have j185_value : Bounds (-922049709116543222022274026708575982829/2000000000000000000000000000000000000000 : ℝ) j185.value (-4610248545582716110111370133356378476539/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h622
  have j185_tangent : Bounds (-10358651797698759534545494670460878413/625000000000000000000000000000000000000 : ℝ) j185.tangent (-165738428763180152552727914062910944393/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj185,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h624
  let v625 : ℝ := j182.value*j185.value
  have h625 : Bounds (-108649914396219407317622471158612640989/10000000000000000000000000000000000000000 : ℝ) v625 (-108649914396219407317622470974913051739/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v626 : ℝ := j182.tangent*j185.value
  have h626 : Bounds (409541040837087757791139278785503653/312500000000000000000000000000000000000 : ℝ) v626 (13105313306786808249316457700178308557/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j182_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v627 : ℝ := j182.value*j185.tangent
  have h627 : Bounds (-1952982135262228432600480790572230837/5000000000000000000000000000000000000000 : ℝ) v627 (-3905964270524456865200961559039043197/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j182_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v628 : ℝ := v626+v627
  have h628 : Bounds (4599674518131175692057747669995827611/5000000000000000000000000000000000000000 : ℝ) v628 (114991862953279392301443701764240817/125000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h626 h627) (by norm_num) (by norm_num)
  obtain ⟨j186,hj186⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j185=z := ⟨_,rfl⟩
  have j186_value : Bounds (-108649914396219407317622471158612640989/10000000000000000000000000000000000000000 : ℝ) j186.value (-108649914396219407317622470974913051739/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h625
  have j186_tangent : Bounds (4599674518131175692057747669995827611/5000000000000000000000000000000000000000 : ℝ) j186.tangent (114991862953279392301443701764240817/125000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj186,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h628
  let v629 : ℝ := j179.value+j186.value
  have h629 : Bounds (52187876353845956380290478560268881443/1250000000000000000000000000000000000000 : ℝ) v629 (417503010830767651042323828905537393183/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_value j186_value) (by norm_num) (by norm_num)
  let v630 : ℝ := j179.tangent+j186.tangent
  have h630 : Bounds (-15655850282961494359591383546259816143/2500000000000000000000000000000000000000 : ℝ) v630 (-15655850282961494359591383116256017399/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j179_tangent j186_tangent) (by norm_num) (by norm_num)
  obtain ⟨j187,hj187⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j179 j186=z := ⟨_,rfl⟩
  have j187_value : Bounds (52187876353845956380290478560268881443/1250000000000000000000000000000000000000 : ℝ) j187.value (417503010830767651042323828905537393183/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h629
  have j187_tangent : Bounds (-15655850282961494359591383546259816143/2500000000000000000000000000000000000000 : ℝ) j187.tangent (-15655850282961494359591383116256017399/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj187,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h630
  let v631 : ℝ := j158.value*j158.value
  have h631 : Bounds (16832046367336787281321280388156425739/10000000000000000000000000000000000000000 : ℝ) v631 (16832046367336787281321280388859665687/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v632 : ℝ := j158.tangent*j158.value
  have h632 : Bounds (10663537845944803229773616694267949123/5000000000000000000000000000000000000000 : ℝ) v632 (5331768922972401614886808347358534679/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v633 : ℝ := j158.value*j158.tangent
  have h633 : Bounds (10663537845944803229773616694267949123/5000000000000000000000000000000000000000 : ℝ) v633 (5331768922972401614886808347358534679/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v634 : ℝ := v632+v633
  have h634 : Bounds (10663537845944803229773616694267949123/2500000000000000000000000000000000000000 : ℝ) v634 (5331768922972401614886808347358534679/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h632 h633) (by norm_num) (by norm_num)
  obtain ⟨j188,hj188⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j158=z := ⟨_,rfl⟩
  have j188_value : Bounds (16832046367336787281321280388156425739/10000000000000000000000000000000000000000 : ℝ) j188.value (16832046367336787281321280388859665687/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h631
  have j188_tangent : Bounds (10663537845944803229773616694267949123/2500000000000000000000000000000000000000 : ℝ) j188.tangent (5331768922972401614886808347358534679/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj188,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h634
  let v635 : ℝ := j167.value*j188.value
  have h635 : Bounds (184489050244669997111412834170943584049/10000000000000000000000000000000000000000 : ℝ) v635 (184489050244669997111412834181720956179/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v636 : ℝ := j167.tangent*j188.value
  have h636 : Bounds (-227124813542658459226884344446103799539/10000000000000000000000000000000000000000 : ℝ) v636 (-28390601692832307403360543053121137587/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j188_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v637 : ℝ := j167.value*j188.tangent
  have h637 : Bounds (58439298660205729969946340469853565051/1250000000000000000000000000000000000000 : ℝ) v637 (467514389281645839759570723786297309397/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j188_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v638 : ℝ := v636+v637
  have h638 : Bounds (240389575738987380532686379312724720869/10000000000000000000000000000000000000000 : ℝ) v638 (240389575738987380532686379361328208701/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h636 h637) (by norm_num) (by norm_num)
  obtain ⟨j189,hj189⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j188=z := ⟨_,rfl⟩
  have j189_value : Bounds (184489050244669997111412834170943584049/10000000000000000000000000000000000000000 : ℝ) j189.value (184489050244669997111412834181720956179/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h635
  have j189_tangent : Bounds (240389575738987380532686379312724720869/10000000000000000000000000000000000000000 : ℝ) j189.tangent (240389575738987380532686379361328208701/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj189,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h638
  let v639 : ℝ := j187.value+j189.value
  have h639 : Bounds (601992061075437648153736662653094635593/10000000000000000000000000000000000000000 : ℝ) v639 (300996030537718824076868331543629174681/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_value j189_value) (by norm_num) (by norm_num)
  let v640 : ℝ := j187.tangent+j189.tangent
  have h640 : Bounds (177766174607141403094320845127685456297/10000000000000000000000000000000000000000 : ℝ) v640 (35553234921428280618864169379260827821/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j187_tangent j189_tangent) (by norm_num) (by norm_num)
  obtain ⟨j190,hj190⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j187 j189=z := ⟨_,rfl⟩
  have j190_value : Bounds (601992061075437648153736662653094635593/10000000000000000000000000000000000000000 : ℝ) j190.value (300996030537718824076868331543629174681/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h639
  have j190_tangent : Bounds (177766174607141403094320845127685456297/10000000000000000000000000000000000000000 : ℝ) j190.tangent (35553234921428280618864169379260827821/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj190,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h640
  let v641 : ℝ := j151.value*j164.value
  have h641 : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) v641 (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v642 : ℝ := j151.tangent*j164.value
  have h642 : Bounds (0 : ℝ) v642 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v643 : ℝ := j151.value*j164.tangent
  have h643 : Bounds (51114504461814199533798455271063457907/1000000000000000000000000000000000000000 : ℝ) v643 (102229008923628399067596910543758293209/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j151_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v644 : ℝ := v642+v643
  have h644 : Bounds (51114504461814199533798455271063457907/1000000000000000000000000000000000000000 : ℝ) v644 (102229008923628399067596910543758293209/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h642 h643) (by norm_num) (by norm_num)
  obtain ⟨j191,hj191⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j151 j164=z := ⟨_,rfl⟩
  have j191_value : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) j191.value (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h641
  have j191_tangent : Bounds (51114504461814199533798455271063457907/1000000000000000000000000000000000000000 : ℝ) j191.tangent (102229008923628399067596910543758293209/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj191,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h644
  let v645 : ℝ := j167.value*j191.value
  have h645 : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) v645 (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v646 : ℝ := j167.tangent*j191.value
  have h646 : Bounds (-5675685575442644273962028028372124366727/10000000000000000000000000000000000000000 : ℝ) v646 (-567568557544264427396202802800001190389/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j191_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v647 : ℝ := j167.value*j191.tangent
  have h647 : Bounds (5602447959142058657230621185091264820497/10000000000000000000000000000000000000000 : ℝ) v647 (5602447959142058657230621185273880255967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j191_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v648 : ℝ := v646+v647
  have h648 : Bounds (-7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) v648 (-73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h646 h647) (by norm_num) (by norm_num)
  obtain ⟨j192,hj192⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j191=z := ⟨_,rfl⟩
  have j192_value : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) j192.value (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h645
  have j192_tangent : Bounds (-7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) j192.tangent (-73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj192,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h648
  let v649 : ℝ := -j192.value
  have h649 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v649 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_value) (by norm_num) (by norm_num)
  let v650 : ℝ := j6.value+v649
  have h650 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v650 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h649) (by norm_num) (by norm_num)
  let v651 : ℝ := -j192.tangent
  have h651 : Bounds (73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) v651 (7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j192_tangent) (by norm_num) (by norm_num)
  let v652 : ℝ := j6.tangent+v651
  have h652 : Bounds (73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) v652 (7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h651) (by norm_num) (by norm_num)
  obtain ⟨j193,hj193⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j192=z := ⟨_,rfl⟩
  have j193_value : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) j193.value (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h650
  have j193_tangent : Bounds (73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) j193.tangent (7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj193,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h652
  let v653 : ℝ := j176.value*j193.value
  have h653 : Bounds (-349757858312048446604033745818953581701/10000000000000000000000000000000000000000 : ℝ) v653 (-349757858312048446604033745655286327909/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j176_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v654 : ℝ := j176.tangent*j193.value
  have h654 : Bounds (42187666140026318856218261755860410383/10000000000000000000000000000000000000000 : ℝ) v654 (10546916535006579714054565585480843523/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j176_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v655 : ℝ := j176.value*j193.tangent
  have h655 : Bounds (5556193244660459089979541645707591573/10000000000000000000000000000000000000000 : ℝ) v655 (5556193244660459089979541690220341293/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j176_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v656 : ℝ := v654+v655
  have h656 : Bounds (11935964846171694486549450850392000489/2500000000000000000000000000000000000000 : ℝ) v656 (9548771876937355589239560806428743077/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h654 h655) (by norm_num) (by norm_num)
  obtain ⟨j194,hj194⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j176 j193=z := ⟨_,rfl⟩
  have j194_value : Bounds (-349757858312048446604033745818953581701/10000000000000000000000000000000000000000 : ℝ) j194.value (-349757858312048446604033745655286327909/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h653
  have j194_tangent : Bounds (11935964846171694486549450850392000489/2500000000000000000000000000000000000000 : ℝ) j194.tangent (9548771876937355589239560806428743077/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj194,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h656
  let v657 : ℝ := j167.value*j165.value
  have h657 : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) v657 (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v658 : ℝ := j167.tangent*j165.value
  have h658 : Bounds (-2134532861248432603559960406385108798513/2500000000000000000000000000000000000000 : ℝ) v658 (-4269065722496865207119920812496626878787/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j165_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v659 : ℝ := j167.value*j165.tangent
  have h659 : Bounds (8427957548575296838094607120941828690543/10000000000000000000000000000000000000000 : ℝ) v659 (4213978774287648419047303560602052870659/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j165_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v660 : ℝ := v658+v659
  have h660 : Bounds (-110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) v660 (-860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h658 h659) (by norm_num) (by norm_num)
  obtain ⟨j195,hj195⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j165=z := ⟨_,rfl⟩
  have j195_value : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) j195.value (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h657
  have j195_tangent : Bounds (-110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) j195.tangent (-860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj195,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h660
  let v661 : ℝ := -j195.value
  have h661 : Bounds (-6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) v661 (-3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_value) (by norm_num) (by norm_num)
  let v662 : ℝ := j0.value+v661
  have h662 : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) v662 (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h661) (by norm_num) (by norm_num)
  let v663 : ℝ := -j195.tangent
  have h663 : Bounds (860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) v663 (110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j195_tangent) (by norm_num) (by norm_num)
  let v664 : ℝ := j0.tangent+v663
  have h664 : Bounds (860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) v664 (110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h663) (by norm_num) (by norm_num)
  obtain ⟨j196,hj196⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j195=z := ⟨_,rfl⟩
  have j196_value : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) j196.value (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h662
  have j196_tangent : Bounds (860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) j196.tangent (110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj196,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h664
  let v665 : ℝ := j182.value*j196.value
  have h665 : Bounds (9028069488688830515669321142338359161/1250000000000000000000000000000000000000 : ℝ) v665 (36112277954755322062677284631356131203/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v666 : ℝ := j182.tangent*j196.value
  have h666 : Bounds (-4355849882154223957573017741072838553/5000000000000000000000000000000000000000 : ℝ) v666 (-272240617634638997348313592626643273/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j182_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v667 : ℝ := j182.value*j196.tangent
  have h667 : Bounds (129823634194626111435698975452620831/500000000000000000000000000000000000000 : ℝ) v667 (162279542743282639294623720775868807/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j182_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v668 : ℝ := v666+v667
  have h668 : Bounds (-3057613540207962843216027986546630243/5000000000000000000000000000000000000000 : ℝ) v668 (-382201692525995355402003464477417739/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h666 h667) (by norm_num) (by norm_num)
  obtain ⟨j197,hj197⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j182 j196=z := ⟨_,rfl⟩
  have j197_value : Bounds (9028069488688830515669321142338359161/1250000000000000000000000000000000000000 : ℝ) j197.value (36112277954755322062677284631356131203/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h665
  have j197_tangent : Bounds (-3057613540207962843216027986546630243/5000000000000000000000000000000000000000 : ℝ) j197.tangent (-382201692525995355402003464477417739/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj197,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h668
  let v669 : ℝ := j194.value+j197.value
  have h669 : Bounds (-277533302402537802478679176680246708413/10000000000000000000000000000000000000000 : ℝ) v669 (-277533302402537802478679176392574065503/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_value j197_value) (by norm_num) (by norm_num)
  let v670 : ℝ := j194.tangent+j197.tangent
  have h670 : Bounds (4162863230427085225976574742847474147/1000000000000000000000000000000000000000 : ℝ) v670 (41628632304270852259765748600505031561/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j194_tangent j197_tangent) (by norm_num) (by norm_num)
  obtain ⟨j198,hj198⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j194 j197=z := ⟨_,rfl⟩
  have j198_value : Bounds (-277533302402537802478679176680246708413/10000000000000000000000000000000000000000 : ℝ) j198.value (-277533302402537802478679176392574065503/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h669
  have j198_tangent : Bounds (4162863230427085225976574742847474147/1000000000000000000000000000000000000000 : ℝ) j198.tangent (41628632304270852259765748600505031561/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj198,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h670
  let v671 : ℝ := j158.value*j164.value
  have h671 : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) v671 (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v672 : ℝ := j158.tangent*j164.value
  have h672 : Bounds (4010382824556015959829411966188649177/1250000000000000000000000000000000000000 : ℝ) v672 (8020765649112031919658823932626861879/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v673 : ℝ := j158.value*j164.tangent
  have h673 : Bounds (30770525891817183779559513613074753021/10000000000000000000000000000000000000000 : ℝ) v673 (30770525891817183779559513614073134897/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j158_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v674 : ℝ := v672+v673
  have h674 : Bounds (62853588488265311458194809342583946437/10000000000000000000000000000000000000000 : ℝ) v674 (62853588488265311458194809344580582413/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h672 h673) (by norm_num) (by norm_num)
  obtain ⟨j199,hj199⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j158 j164=z := ⟨_,rfl⟩
  have j199_value : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) j199.value (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h671
  have j199_tangent : Bounds (62853588488265311458194809342583946437/10000000000000000000000000000000000000000 : ℝ) j199.tangent (62853588488265311458194809344580582413/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj199,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h674
  let v675 : ℝ := j167.value*j199.value
  have h675 : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) v675 (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v676 : ℝ := j167.tangent*j199.value
  have h676 : Bounds (-170835882878842439262186524568416224971/5000000000000000000000000000000000000000 : ℝ) v676 (-85417941439421219631093262277199524627/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j199_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v677 : ℝ := j167.value*j199.tangent
  have h677 : Bounds (137782401397984147685167287355602429351/2000000000000000000000000000000000000000 : ℝ) v677 (137782401397984147685167287362271654607/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j199_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v678 : ℝ := v676+v677
  have h678 : Bounds (347240241232235859901463387641179696813/10000000000000000000000000000000000000000 : ℝ) v678 (347240241232235859901463387702560174527/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h676 h677) (by norm_num) (by norm_num)
  obtain ⟨j200,hj200⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j199=z := ⟨_,rfl⟩
  have j200_value : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) j200.value (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h675
  have j200_tangent : Bounds (347240241232235859901463387641179696813/10000000000000000000000000000000000000000 : ℝ) j200.tangent (347240241232235859901463387702560174527/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj200,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h678
  let v679 : ℝ := j198.value+j200.value
  have h679 : Bounds (-37506091341/2500000000000000000000000000000000000000 : ℝ) v679 (150807438027/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_value j200_value) (by norm_num) (by norm_num)
  let v680 : ℝ := j198.tangent+j200.tangent
  have h680 : Bounds (388868873536506712161229135069654438283/10000000000000000000000000000000000000000 : ℝ) v680 (48608609192063339020153642037883150761/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j198_tangent j200_tangent) (by norm_num) (by norm_num)
  obtain ⟨j201,hj201⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j198 j200=z := ⟨_,rfl⟩
  have j201_value : Bounds (-37506091341/2500000000000000000000000000000000000000 : ℝ) j201.value (150807438027/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h679
  have j201_tangent : Bounds (388868873536506712161229135069654438283/10000000000000000000000000000000000000000 : ℝ) j201.tangent (48608609192063339020153642037883150761/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj201,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h680
  let v681 : ℝ := j164.value*j151.value
  have h681 : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) v681 (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v682 : ℝ := j164.tangent*j151.value
  have h682 : Bounds (51114504461814199533798455271063457907/1000000000000000000000000000000000000000 : ℝ) v682 (102229008923628399067596910543758293209/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j151_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v683 : ℝ := j164.value*j151.tangent
  have h683 : Bounds (0 : ℝ) v683 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j151_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v684 : ℝ := v682+v683
  have h684 : Bounds (51114504461814199533798455271063457907/1000000000000000000000000000000000000000 : ℝ) v684 (102229008923628399067596910543758293209/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h682 h683) (by norm_num) (by norm_num)
  obtain ⟨j202,hj202⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j151=z := ⟨_,rfl⟩
  have j202_value : Bounds (210310360374455809551943758644006748413/5000000000000000000000000000000000000000 : ℝ) j202.value (420620720748911619103887517294023807967/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h681
  have j202_tangent : Bounds (51114504461814199533798455271063457907/1000000000000000000000000000000000000000 : ℝ) j202.tangent (102229008923628399067596910543758293209/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj202,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h684
  let v685 : ℝ := j167.value*j202.value
  have h685 : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) v685 (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v686 : ℝ := j167.tangent*j202.value
  have h686 : Bounds (-5675685575442644273962028028372124366727/10000000000000000000000000000000000000000 : ℝ) v686 (-567568557544264427396202802800001190389/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j202_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v687 : ℝ := j167.value*j202.tangent
  have h687 : Bounds (5602447959142058657230621185091264820497/10000000000000000000000000000000000000000 : ℝ) v687 (5602447959142058657230621185273880255967/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j202_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v688 : ℝ := v686+v687
  have h688 : Bounds (-7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) v688 (-73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h686 h687) (by norm_num) (by norm_num)
  obtain ⟨j203,hj203⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j202=z := ⟨_,rfl⟩
  have j203_value : Bounds (576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) j203.value (1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h685
  have j203_tangent : Bounds (-7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) j203.tangent (-73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj203,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h688
  let v689 : ℝ := -j203.value
  have h689 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v689 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_value) (by norm_num) (by norm_num)
  let v690 : ℝ := j6.value+v689
  have h690 : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) v690 (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_value h689) (by norm_num) (by norm_num)
  let v691 : ℝ := -j203.tangent
  have h691 : Bounds (73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) v691 (7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j203_tangent) (by norm_num) (by norm_num)
  let v692 : ℝ := j6.tangent+v691
  have h692 : Bounds (73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) v692 (7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j6_tangent h691) (by norm_num) (by norm_num)
  obtain ⟨j204,hj204⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j6 j203=z := ⟨_,rfl⟩
  have j204_value : Bounds (-1152562136395679027527842533379247283137/2500000000000000000000000000000000000000 : ℝ) j204.value (-576281068197839513763921266671801152647/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h690
  have j204_tangent : Bounds (73237616300585616731406842726131647923/10000000000000000000000000000000000000000 : ℝ) j204.tangent (7323761630058561673140684328085954623/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj204,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h692
  let v693 : ℝ := j204.value*j115.value
  have h693 : Bounds (-3108405719419768217666238163447733073573/10000000000000000000000000000000000000000 : ℝ) v693 (-3108405719419768217666238163313628083151/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v694 : ℝ := j204.tangent*j115.value
  have h694 : Bounds (24689799599148996618139709690886004223/5000000000000000000000000000000000000000 : ℝ) v694 (24689799599148996618139709878196986017/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j115_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v695 : ℝ := j204.value*j115.tangent
  have h695 : Bounds (-3236783930292953726936223803815273257843/10000000000000000000000000000000000000000 : ℝ) v695 (-647356786058590745387244760733289424063/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j115_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v696 : ℝ := v694+v695
  have h696 : Bounds (-3187404331094655733699944384433501249397/10000000000000000000000000000000000000000 : ℝ) v696 (-3187404331094655733699944383910053148281/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h694 h695) (by norm_num) (by norm_num)
  obtain ⟨j205,hj205⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j115=z := ⟨_,rfl⟩
  have j205_value : Bounds (-3108405719419768217666238163447733073573/10000000000000000000000000000000000000000 : ℝ) j205.value (-3108405719419768217666238163313628083151/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h693
  have j205_tangent : Bounds (-3187404331094655733699944384433501249397/10000000000000000000000000000000000000000 : ℝ) j205.tangent (-3187404331094655733699944383910053148281/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj205,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h696
  let v697 : ℝ := j164.value*j160.value
  have h697 : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) v697 (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v698 : ℝ := j164.tangent*j160.value
  have h698 : Bounds (384466644636715768263951418369970382119/5000000000000000000000000000000000000000 : ℝ) v698 (768933289273431536527902836751076686421/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j160_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v699 : ℝ := j164.value*j160.tangent
  have h699 : Bounds (0 : ℝ) v699 (0 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j160_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v700 : ℝ := v698+v699
  have h700 : Bounds (384466644636715768263951418369970382119/5000000000000000000000000000000000000000 : ℝ) v700 (768933289273431536527902836751076686421/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h698 h699) (by norm_num) (by norm_num)
  obtain ⟨j206,hj206⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j160=z := ⟨_,rfl⟩
  have j206_value : Bounds (39547149794786289059721189741544253487/625000000000000000000000000000000000000 : ℝ) j206.value (39547149794786289059721189742050986101/625000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h697
  have j206_tangent : Bounds (384466644636715768263951418369970382119/5000000000000000000000000000000000000000 : ℝ) j206.tangent (768933289273431536527902836751076686421/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj206,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h700
  let v701 : ℝ := j167.value*j206.value
  have h701 : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) v701 (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v702 : ℝ := j167.tangent*j206.value
  have h702 : Bounds (-2134532861248432603559960406385108798513/2500000000000000000000000000000000000000 : ℝ) v702 (-4269065722496865207119920812496626878787/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j206_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v703 : ℝ := j167.value*j206.tangent
  have h703 : Bounds (8427957548575296838094607120941828690543/10000000000000000000000000000000000000000 : ℝ) v703 (4213978774287648419047303560602052870659/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j206_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v704 : ℝ := v702+v703
  have h704 : Bounds (-110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) v704 (-860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h702 h703) (by norm_num) (by norm_num)
  obtain ⟨j207,hj207⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j206=z := ⟨_,rfl⟩
  have j207_value : Bounds (3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) j207.value (6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h701
  have j207_tangent : Bounds (-110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) j207.tangent (-860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj207,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h704
  let v705 : ℝ := -j207.value
  have h705 : Bounds (-6935357421240957955854598009045288983947/10000000000000000000000000000000000000000 : ℝ) v705 (-3467678710620478977927299004420518017531/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_value) (by norm_num) (by norm_num)
  let v706 : ℝ := j0.value+v705
  have h706 : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) v706 (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_value h705) (by norm_num) (by norm_num)
  let v707 : ℝ := -j207.tangent
  have h707 : Bounds (860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) v707 (110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j207_tangent) (by norm_num) (by norm_num)
  let v708 : ℝ := j0.tangent+v707
  have h708 : Bounds (860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) v708 (110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j0_tangent h707) (by norm_num) (by norm_num)
  obtain ⟨j208,hj208⟩ : ∃ z : LReturnJets.Jet, LReturnJets.sub j0 j207=z := ⟨_,rfl⟩
  have j208_value : Bounds (3064642578759042044145401990954711016053/10000000000000000000000000000000000000000 : ℝ) j208.value (1532321289379521022072700995579481982469/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h706
  have j208_tangent : Bounds (860733565769012313634644560852718877/78125000000000000000000000000000000000 : ℝ) j208.tangent (110173896418433576145234504598606503509/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj208,LReturnJets.sub,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h708
  let v709 : ℝ := j208.value*j144.value
  have h709 : Bounds (2604094496409338938072053552706227758953/10000000000000000000000000000000000000000 : ℝ) v709 (651023624102334734518013388224817224351/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v710 : ℝ := j208.tangent*j144.value
  have h710 : Bounds (9361719350234651357813490167349137197/1000000000000000000000000000000000000000 : ℝ) v710 (46808596751173256789067451181003269709/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j144_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v711 : ℝ := j208.value*j144.tangent
  have h711 : Bounds (3154616974582134600800794084778189812657/10000000000000000000000000000000000000000 : ℝ) v711 (1577308487291067300400397042507813713041/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j144_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v712 : ℝ := v710+v711
  have h712 : Bounds (3248234168084481114378928986451681184627/10000000000000000000000000000000000000000 : ℝ) v712 (6496468336168962228757857974755267931/20000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h710 h711) (by norm_num) (by norm_num)
  obtain ⟨j209,hj209⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j144=z := ⟨_,rfl⟩
  have j209_value : Bounds (2604094496409338938072053552706227758953/10000000000000000000000000000000000000000 : ℝ) j209.value (651023624102334734518013388224817224351/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h709
  have j209_tangent : Bounds (3248234168084481114378928986451681184627/10000000000000000000000000000000000000000 : ℝ) j209.tangent (6496468336168962228757857974755267931/20000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj209,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h712
  let v713 : ℝ := j205.value+j209.value
  have h713 : Bounds (-25215561150521463979709230537075265731/500000000000000000000000000000000000000 : ℝ) v713 (-504311223010429279594184610414359185747/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_value j209_value) (by norm_num) (by norm_num)
  let v714 : ℝ := j205.tangent+j209.tangent
  have h714 : Bounds (6082983698982538067898460201817993523/1000000000000000000000000000000000000000 : ℝ) v714 (60829836989825380678984603467580817219/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j205_tangent j209_tangent) (by norm_num) (by norm_num)
  obtain ⟨j210,hj210⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j205 j209=z := ⟨_,rfl⟩
  have j210_value : Bounds (-25215561150521463979709230537075265731/500000000000000000000000000000000000000 : ℝ) j210.value (-504311223010429279594184610414359185747/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h713
  have j210_tangent : Bounds (6082983698982538067898460201817993523/1000000000000000000000000000000000000000 : ℝ) j210.tangent (60829836989825380678984603467580817219/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj210,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h714
  let v715 : ℝ := j210.value*j178.value
  have h715 : Bounds (-349757858312048446604033745853803888681/10000000000000000000000000000000000000000 : ℝ) v715 (-174878929156024223302016872810218010463/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v716 : ℝ := j210.tangent*j178.value
  have h716 : Bounds (2109383307001315942810913077294770311/500000000000000000000000000000000000000 : ℝ) v716 (1318364566875822464256820704746511817/312500000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j210_tangent j178_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v717 : ℝ := j210.value*j178.tangent
  have h717 : Bounds (5556193244660459089979541654739235849/10000000000000000000000000000000000000000 : ℝ) v717 (5556193244660459089979541681188697023/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j178_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v718 : ℝ := v716+v717
  have h718 : Bounds (47743859384686777946197803200634642069/10000000000000000000000000000000000000000 : ℝ) v718 (47743859384686777946197804233077075167/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h716 h717) (by norm_num) (by norm_num)
  obtain ⟨j211,hj211⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j178=z := ⟨_,rfl⟩
  have j211_value : Bounds (-349757858312048446604033745853803888681/10000000000000000000000000000000000000000 : ℝ) j211.value (-174878929156024223302016872810218010463/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h715
  have j211_tangent : Bounds (47743859384686777946197803200634642069/10000000000000000000000000000000000000000 : ℝ) j211.tangent (47743859384686777946197804233077075167/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj211,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h718
  let v719 : ℝ := j204.value*j126.value
  have h719 : Bounds (-391743002849372285995308374772555903911/1000000000000000000000000000000000000000 : ℝ) v719 (-3917430028493722859953083747575096940167/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v720 : ℝ := j204.tangent*j126.value
  have h720 : Bounds (62231620372422260933708227486568486259/10000000000000000000000000000000000000000 : ℝ) v720 (31115810186211130466854113979199314901/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j204_tangent j126_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v721 : ℝ := j204.value*j126.tangent
  have h721 : Bounds (-4745600162230639122452184894643203915741/10000000000000000000000000000000000000000 : ℝ) v721 (-949120032446127824490436978891107623671/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j204_value j126_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v722 : ℝ := v720+v721
  have h722 : Bounds (-2341684270929108430759238333578317714741/5000000000000000000000000000000000000000 : ℝ) v722 (-4683368541858216861518476666497139488553/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h720 h721) (by norm_num) (by norm_num)
  obtain ⟨j212,hj212⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j204 j126=z := ⟨_,rfl⟩
  have j212_value : Bounds (-391743002849372285995308374772555903911/1000000000000000000000000000000000000000 : ℝ) j212.value (-3917430028493722859953083747575096940167/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h719
  have j212_tangent : Bounds (-2341684270929108430759238333578317714741/5000000000000000000000000000000000000000 : ℝ) j212.tangent (-4683368541858216861518476666497139488553/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj212,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h722
  let v723 : ℝ := j208.value*j150.value
  have h723 : Bounds (3760769156101686211723610826750157536539/10000000000000000000000000000000000000000 : ℝ) v723 (11752403612817769411636283834391607857/31250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v724 : ℝ := j208.tangent*j150.value
  have h724 : Bounds (135199645899902658589180076436772533043/10000000000000000000000000000000000000000 : ℝ) v724 (33799911474975664647295019357564937299/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_tangent j150_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v725 : ℝ := j208.value*j150.tangent
  have h725 : Bounds (456706527362249787124468713590934341973/1000000000000000000000000000000000000000 : ℝ) v725 (570883159202812233905585892028017813521/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j208_value j150_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v726 : ℝ := v724+v725
  have h726 : Bounds (4702264919522400529833867212346115952773/10000000000000000000000000000000000000000 : ℝ) v726 (1175566229880600132458466803413600564341/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h724 h725) (by norm_num) (by norm_num)
  obtain ⟨j213,hj213⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j208 j150=z := ⟨_,rfl⟩
  have j213_value : Bounds (3760769156101686211723610826750157536539/10000000000000000000000000000000000000000 : ℝ) j213.value (11752403612817769411636283834391607857/31250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h723
  have j213_tangent : Bounds (4702264919522400529833867212346115952773/10000000000000000000000000000000000000000 : ℝ) j213.tangent (1175566229880600132458466803413600564341/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj213,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h726
  let v727 : ℝ := j212.value+j213.value
  have h727 : Bounds (-156660872392036648229472920975401502571/10000000000000000000000000000000000000000 : ℝ) v727 (-156660872392036648229472920569782425927/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_value j213_value) (by norm_num) (by norm_num)
  let v728 : ℝ := j212.tangent+j213.tangent
  have h728 : Bounds (18896377664183668315390545189480523291/10000000000000000000000000000000000000000 : ℝ) v728 (18896377664183668315390547157262768811/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j212_tangent j213_tangent) (by norm_num) (by norm_num)
  obtain ⟨j214,hj214⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j212 j213=z := ⟨_,rfl⟩
  have j214_value : Bounds (-156660872392036648229472920975401502571/10000000000000000000000000000000000000000 : ℝ) j214.value (-156660872392036648229472920569782425927/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h727
  have j214_tangent : Bounds (18896377664183668315390545189480523291/10000000000000000000000000000000000000000 : ℝ) j214.tangent (18896377664183668315390547157262768811/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj214,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h728
  let v729 : ℝ := j214.value*j185.value
  have h729 : Bounds (72224555909510644125354569105748456041/10000000000000000000000000000000000000000 : ℝ) v729 (72224555909510644125354569295670679649/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v730 : ℝ := j214.tangent*j185.value
  have h730 : Bounds (-8711699764308447915146035676873602723/10000000000000000000000000000000000000000 : ℝ) v730 (-8711699764308447915146034769324659019/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j214_tangent j185_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v731 : ℝ := j214.value*j185.tangent
  have h731 : Bounds (2596472683892522228713979512167056819/10000000000000000000000000000000000000000 : ℝ) v731 (649118170973130557178494882324815179/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j214_value j185_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v732 : ℝ := v730+v731
  have h732 : Bounds (-382201692525995355402003510294159119/625000000000000000000000000000000000000 : ℝ) v732 (-6115227080415925686432055240025398303/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h730 h731) (by norm_num) (by norm_num)
  obtain ⟨j215,hj215⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j185=z := ⟨_,rfl⟩
  have j215_value : Bounds (72224555909510644125354569105748456041/10000000000000000000000000000000000000000 : ℝ) j215.value (72224555909510644125354569295670679649/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h729
  have j215_tangent : Bounds (-382201692525995355402003510294159119/625000000000000000000000000000000000000 : ℝ) j215.tangent (-6115227080415925686432055240025398303/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj215,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h732
  let v733 : ℝ := j211.value+j215.value
  have h733 : Bounds (-867291570007930632745872427337673227/31250000000000000000000000000000000000 : ℝ) v733 (-277533302402537802478679176324765341277/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_value j215_value) (by norm_num) (by norm_num)
  let v734 : ℝ := j211.tangent+j215.tangent
  have h734 : Bounds (8325726460854170451953149407185619233/2000000000000000000000000000000000000000 : ℝ) v734 (650447379754232066558839828016432451/156250000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j211_tangent j215_tangent) (by norm_num) (by norm_num)
  obtain ⟨j216,hj216⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j211 j215=z := ⟨_,rfl⟩
  have j216_value : Bounds (-867291570007930632745872427337673227/31250000000000000000000000000000000000 : ℝ) j216.value (-277533302402537802478679176324765341277/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h733
  have j216_tangent : Bounds (8325726460854170451953149407185619233/2000000000000000000000000000000000000000 : ℝ) j216.tangent (650447379754232066558839828016432451/156250000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj216,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h734
  let v735 : ℝ := j164.value*j158.value
  have h735 : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) v735 (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v736 : ℝ := j164.tangent*j158.value
  have h736 : Bounds (30770525891817183779559513613074753021/10000000000000000000000000000000000000000 : ℝ) v736 (30770525891817183779559513614073134897/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j158_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v737 : ℝ := j164.value*j158.tangent
  have h737 : Bounds (4010382824556015959829411966188649177/1250000000000000000000000000000000000000 : ℝ) v737 (8020765649112031919658823932626861879/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j158_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v738 : ℝ := v736+v737
  have h738 : Bounds (62853588488265311458194809342583946437/10000000000000000000000000000000000000000 : ℝ) v738 (62853588488265311458194809344580582413/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h736 h737) (by norm_num) (by norm_num)
  obtain ⟨j217,hj217⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j158=z := ⟨_,rfl⟩
  have j217_value : Bounds (6330258365366835175730593417239996913/2500000000000000000000000000000000000000 : ℝ) j217.value (49455143479428399810395261073709563/19531250000000000000000000000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h735
  have j217_tangent : Bounds (62853588488265311458194809342583946437/10000000000000000000000000000000000000000 : ℝ) j217.tangent (62853588488265311458194809344580582413/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj217,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h738
  let v739 : ℝ := j167.value*j217.value
  have h739 : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) v739 (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v740 : ℝ := j167.tangent*j217.value
  have h740 : Bounds (-170835882878842439262186524568416224971/5000000000000000000000000000000000000000 : ℝ) v740 (-85417941439421219631093262277199524627/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j217_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v741 : ℝ := j167.value*j217.tangent
  have h741 : Bounds (137782401397984147685167287355602429351/2000000000000000000000000000000000000000 : ℝ) v741 (137782401397984147685167287362271654607/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j217_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v742 : ℝ := v740+v741
  have h742 : Bounds (347240241232235859901463387641179696813/10000000000000000000000000000000000000000 : ℝ) v742 (347240241232235859901463387702560174527/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h740 h741) (by norm_num) (by norm_num)
  obtain ⟨j218,hj218⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j217=z := ⟨_,rfl⟩
  have j218_value : Bounds (277533302402537802478679176530222343049/10000000000000000000000000000000000000000 : ℝ) j218.value (27753330240253780247867917654338150353/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h739
  have j218_tangent : Bounds (347240241232235859901463387641179696813/10000000000000000000000000000000000000000 : ℝ) j218.tangent (347240241232235859901463387702560174527/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj218,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h742
  let v743 : ℝ := j216.value+j218.value
  have h743 : Bounds (-217833089591/10000000000000000000000000000000000000000 : ℝ) v743 (218616162253/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_value j218_value) (by norm_num) (by norm_num)
  let v744 : ℝ := j216.tangent+j218.tangent
  have h744 : Bounds (194434436768253356080614567338553896489/5000000000000000000000000000000000000000 : ℝ) v744 (388868873536506712161229136695611851391/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j216_tangent j218_tangent) (by norm_num) (by norm_num)
  obtain ⟨j219,hj219⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j216 j218=z := ⟨_,rfl⟩
  have j219_value : Bounds (-217833089591/10000000000000000000000000000000000000000 : ℝ) j219.value (218616162253/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h743
  have j219_tangent : Bounds (194434436768253356080614567338553896489/5000000000000000000000000000000000000000 : ℝ) j219.tangent (388868873536506712161229136695611851391/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj219,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h744
  let v745 : ℝ := j210.value*j193.value
  have h745 : Bounds (232500008240487238023263283802829985949/10000000000000000000000000000000000000000 : ℝ) v745 (232500008240487238023263283960842947381/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pp j210_value j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v746 : ℝ := j210.tangent*j193.value
  have h746 : Bounds (-28044066751037616706877966268971702109/10000000000000000000000000000000000000000 : ℝ) v746 (-1752754171939851044179872849993410001/625000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j210_tangent j193_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v747 : ℝ := j210.value*j193.tangent
  have h747 : Bounds (-738691036938337671344709348780354189/2000000000000000000000000000000000000000 : ℝ) v747 (-738691036938337671344709342706056039/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j210_value j193_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v748 : ℝ := v746+v747
  have h748 : Bounds (-15868760967864652531800756506436736527/5000000000000000000000000000000000000000 : ℝ) v748 (-31737521935729305063601512313424840211/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h746 h747) (by norm_num) (by norm_num)
  obtain ⟨j220,hj220⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j210 j193=z := ⟨_,rfl⟩
  have j220_value : Bounds (232500008240487238023263283802829985949/10000000000000000000000000000000000000000 : ℝ) j220.value (232500008240487238023263283960842947381/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h745
  have j220_tangent : Bounds (-15868760967864652531800756506436736527/5000000000000000000000000000000000000000 : ℝ) j220.tangent (-31737521935729305063601512313424840211/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj220,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h748
  let v749 : ℝ := j214.value*j196.value
  have h749 : Bounds (-48010957995817240911850449769675533703/10000000000000000000000000000000000000000 : ℝ) v749 (-24005478997908620455925224821083969941/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v750 : ℝ := j214.tangent*j196.value
  have h750 : Bounds (5791064357396860066074088561005160247/10000000000000000000000000000000000000000 : ℝ) v750 (5791064357396860066074089164446049869/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j214_tangent j196_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v751 : ℝ := j214.value*j196.tangent
  have h751 : Bounds (-107874617048385537420341666024471749/625000000000000000000000000000000000000 : ℝ) v751 (-431498468193542149681366659810409323/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j214_value j196_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v752 : ℝ := v750+v751
  have h752 : Bounds (4065070484622691467348621904613612263/10000000000000000000000000000000000000000 : ℝ) v752 (4065070484622691467348622525204412577/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h750 h751) (by norm_num) (by norm_num)
  obtain ⟨j221,hj221⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j214 j196=z := ⟨_,rfl⟩
  have j221_value : Bounds (-48010957995817240911850449769675533703/10000000000000000000000000000000000000000 : ℝ) j221.value (-24005478997908620455925224821083969941/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h749
  have j221_tangent : Bounds (4065070484622691467348621904613612263/10000000000000000000000000000000000000000 : ℝ) j221.tangent (4065070484622691467348622525204412577/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj221,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h752
  let v753 : ℝ := j220.value+j221.value
  have h753 : Bounds (92244525122334998555706417016577226123/5000000000000000000000000000000000000000 : ℝ) v753 (184489050244669997111412834318675007499/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_value j221_value) (by norm_num) (by norm_num)
  let v754 : ℝ := j220.tangent+j221.tangent
  have h754 : Bounds (-27672451451106613596252891108259860791/10000000000000000000000000000000000000000 : ℝ) v754 (-13836225725553306798126444894110213817/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j220_tangent j221_tangent) (by norm_num) (by norm_num)
  obtain ⟨j222,hj222⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j220 j221=z := ⟨_,rfl⟩
  have j222_value : Bounds (92244525122334998555706417016577226123/5000000000000000000000000000000000000000 : ℝ) j222.value (184489050244669997111412834318675007499/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h753
  have j222_tangent : Bounds (-27672451451106613596252891108259860791/10000000000000000000000000000000000000000 : ℝ) j222.tangent (-13836225725553306798126444894110213817/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj222,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h754
  let v755 : ℝ := j164.value*j164.value
  have h755 : Bounds (1904565617169797534184441459407627811/500000000000000000000000000000000000000 : ℝ) v755 (19045656171697975341844414594452895001/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v756 : ℝ := j164.tangent*j164.value
  have h756 : Bounds (46289173563922876214673355456264718489/10000000000000000000000000000000000000000 : ℝ) v756 (9257834712784575242934671091451462643/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_tangent j164_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v757 : ℝ := j164.value*j164.tangent
  have h757 : Bounds (46289173563922876214673355456264718489/10000000000000000000000000000000000000000 : ℝ) v757 (9257834712784575242934671091451462643/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j164_value j164_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v758 : ℝ := v756+v757
  have h758 : Bounds (46289173563922876214673355456264718489/5000000000000000000000000000000000000000 : ℝ) v758 (9257834712784575242934671091451462643/1000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h756 h757) (by norm_num) (by norm_num)
  obtain ⟨j223,hj223⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j164 j164=z := ⟨_,rfl⟩
  have j223_value : Bounds (1904565617169797534184441459407627811/500000000000000000000000000000000000000 : ℝ) j223.value (19045656171697975341844414594452895001/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h755
  have j223_tangent : Bounds (46289173563922876214673355456264718489/5000000000000000000000000000000000000000 : ℝ) j223.tangent (9257834712784575242934671091451462643/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj223,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h758
  let v759 : ℝ := j167.value*j223.value
  have h759 : Bounds (417503010830767651042323828686476261117/10000000000000000000000000000000000000000 : ℝ) v759 (104375752707691912760580957175419596003/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v760 : ℝ := j167.tangent*j223.value
  have h760 : Bounds (-102797746926095609199688364823755742769/2000000000000000000000000000000000000000 : ℝ) v760 (-102797746926095609199688364816452185343/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn j167_tangent j223_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v761 : ℝ := j167.value*j223.tangent
  have h761 : Bounds (202942541412925434138216322656048066499/2000000000000000000000000000000000000000 : ℝ) v761 (1014712707064627170691081613318881534467/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j167_value j223_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v762 : ℝ := v760+v761
  have h762 : Bounds (10014479448682982493852795783229232373/200000000000000000000000000000000000000 : ℝ) v762 (62590496554268640586579973654577575969/1250000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h760 h761) (by norm_num) (by norm_num)
  obtain ⟨j224,hj224⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j167 j223=z := ⟨_,rfl⟩
  have j224_value : Bounds (417503010830767651042323828686476261117/10000000000000000000000000000000000000000 : ℝ) j224.value (104375752707691912760580957175419596003/2500000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h759
  have j224_tangent : Bounds (10014479448682982493852795783229232373/200000000000000000000000000000000000000 : ℝ) j224.tangent (62590496554268640586579973654577575969/1250000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj224,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h762
  let v763 : ℝ := j222.value+j224.value
  have h763 : Bounds (601992061075437648153736662719630713363/10000000000000000000000000000000000000000 : ℝ) v763 (601992061075437648153736663020353391511/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_value j224_value) (by norm_num) (by norm_num)
  let v764 : ℝ := j222.tangent+j224.tangent
  have h764 : Bounds (473051520983042511096386898053201757859/10000000000000000000000000000000000000000 : ℝ) v764 (236525760491521255548193449724200090059/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add j222_tangent j224_tangent) (by norm_num) (by norm_num)
  obtain ⟨j225,hj225⟩ : ∃ z : LReturnJets.Jet, LReturnJets.add j222 j224=z := ⟨_,rfl⟩
  have j225_value : Bounds (601992061075437648153736662719630713363/10000000000000000000000000000000000000000 : ℝ) j225.value (601992061075437648153736663020353391511/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h763
  have j225_tangent : Bounds (473051520983042511096386898053201757859/10000000000000000000000000000000000000000 : ℝ) j225.tangent (236525760491521255548193449724200090059/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj225,LReturnJets.add,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h764
  have hm13 : jetIter c d 1 3=!![j190,j201;j219,j225] := by
    rw [jetIter,hm12]
    ext i l <;> fin_cases i <;> fin_cases l
    all_goals simp only [updateJet,stepJet,LReturnJets.inverseUpdate,LReturnJets.matAdd,LReturnJets.matMul,LReturnJets.matSub,LReturnJets.matScale,LReturnJets.matConstant,LReturnJets.outer,LReturnJets.vecScale,LReturnJets.mulVec,LReturnJets.vecConstant,LReturnJets.dot,SeedOrbit.phase,SeedOrbit.gradient,SeedOrbit.nextPhase,SeedOrbit.length,SeedCycle.g0,SeedCycle.g1,SeedCycle.g2,Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.sub_apply,sub_eq_add_neg]
    all_goals norm_num [Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Pi.add_apply,Pi.neg_apply,Matrix.one_apply,← hj0,← hj3,← hj4,← hj6,← hj11,← hj77,← hj78,← hj80,← hj85,← hj151,← hj152,← hj153,← hj154,← hj155,← hj156,← hj157,← hj158,← hj159,← hj160,← hj161,← hj162,← hj163,← hj164,← hj165,← hj166,← hj167,← hj168,← hj169,← hj170,← hj171,← hj172,← hj173,← hj174,← hj175,← hj176,← hj177,← hj178,← hj179,← hj180,← hj181,← hj182,← hj183,← hj184,← hj185,← hj186,← hj187,← hj188,← hj189,← hj190,← hj191,← hj192,← hj193,← hj194,← hj195,← hj196,← hj197,← hj198,← hj199,← hj200,← hj201,← hj202,← hj203,← hj204,← hj205,← hj206,← hj207,← hj208,← hj209,← hj210,← hj211,← hj212,← hj213,← hj214,← hj215,← hj216,← hj217,← hj218,← hj219,← hj220,← hj221,← hj222,← hj223,← hj224,← hj225]
    all_goals rfl
  let v765 : ℝ := j190.value⁻¹
  have h765 : Bounds (16611514746781463610085203381548610845247/1000000000000000000000000000000000000000 : ℝ) v765 (33223029493562927220170406787058059050731/2000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos j190_value (by norm_num)) (by norm_num) (by norm_num)
  let v766 : ℝ := -j190.tangent
  have h766 : Bounds (-35553234921428280618864169379260827821/2000000000000000000000000000000000000000 : ℝ) v766 (-177766174607141403094320845127685456297/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.neg j190_tangent) (by norm_num) (by norm_num)
  let v767 : ℝ := j190.value*j190.value
  have h767 : Bounds (4529930519973168144797654944532041299/1250000000000000000000000000000000000000 : ℝ) v767 (9059861039946336289595309902132238043/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j190_value j190_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v768 : ℝ := v767⁻¹
  have h768 : Bounds (1379712110912690165406980929759475127625339/5000000000000000000000000000000000000000 : ℝ) v768 (4311600346602156766896815411717512948219/15625000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.inv_pos h767 (by norm_num)) (by norm_num) (by norm_num)
  let v769 : ℝ := v766*v768
  have h769 : Bounds (-9810645760643717025503363417278046712409/2000000000000000000000000000000000000000 : ℝ) v769 (-24526614401609292563758408263798892943929/5000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_pn h766 h768 (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  obtain ⟨j226,hj226⟩ : ∃ z : LReturnJets.Jet, LReturnJets.inv j190=z := ⟨_,rfl⟩
  have j226_value : Bounds (16611514746781463610085203381548610845247/1000000000000000000000000000000000000000 : ℝ) j226.value (33223029493562927220170406787058059050731/2000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h765
  have j226_tangent : Bounds (-9810645760643717025503363417278046712409/2000000000000000000000000000000000000000 : ℝ) j226.tangent (-24526614401609292563758408263798892943929/5000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj226,LReturnJets.inv,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h769
  let v770 : ℝ := j201.value*j226.value
  have h770 : Bounds (-2492131957621/10000000000000000000000000000000000000000 : ℝ) v770 (250513998071/1000000000000000000000000000000000000000 : ℝ) := by
    exact mul_corners j201_value j226_value (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v771 : ℝ := j201.tangent*j226.value
  have h771 : Bounds (6459701027315977292157840251773444940797/10000000000000000000000000000000000000000 : ℝ) v771 (6459701027315977292157840276921078015663/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j201_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v772 : ℝ := j201.value*j226.tangent
  have h772 : Bounds (-739759176277/10000000000000000000000000000000000000000 : ℝ) v772 (367958976013/5000000000000000000000000000000000000000 : ℝ) := by
    exact mul_corners j201_value j226_tangent (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v773 : ℝ := v771+v772
  have h773 : Bounds (161492525682899432303946006275842144113/250000000000000000000000000000000000000 : ℝ) v773 (6459701027315977292157840277656995967689/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h771 h772) (by norm_num) (by norm_num)
  obtain ⟨j227,hj227⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j201 j226=z := ⟨_,rfl⟩
  have j227_value : Bounds (-2492131957621/10000000000000000000000000000000000000000 : ℝ) j227.value (250513998071/1000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h770
  have j227_tangent : Bounds (161492525682899432303946006275842144113/250000000000000000000000000000000000000 : ℝ) j227.tangent (6459701027315977292157840277656995967689/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj227,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h773
  have he01 : jacobian c d 0 1=j227.tangent := by
    simp only [jacobian,shapeJet,hm13,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj227,← hj226]
    rfl
  let v774 : ℝ := j225.value*j226.value
  have h774 : Bounds (4999999999999999999999999996946574051639/5000000000000000000000000000000000000000 : ℝ) v774 (10000000000000000000000000006100724239817/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_value j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v775 : ℝ := j225.tangent*j226.value
  have h775 : Bounds (7858102316797211638366204323071276116881/10000000000000000000000000000000000000000 : ℝ) v775 (7858102316797211638366204351914990561567/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_nn j225_tangent j226_value (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v776 : ℝ := j225.value*j226.tangent
  have h776 : Bounds (-2952965430965457970967974112848442902153/10000000000000000000000000000000000000000 : ℝ) v776 (-738241357741364492741993519433609834881/2500000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.mul_np j225_value j226_tangent (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  let v777 : ℝ := v775+v776
  have h777 : Bounds (613142110728969208424778776277854151841/1250000000000000000000000000000000000000 : ℝ) v777 (4905136885831753667398230274180551222043/10000000000000000000000000000000000000000 : ℝ) := by
    exact enlarge (IntervalBounds.add h775 h776) (by norm_num) (by norm_num)
  obtain ⟨j228,hj228⟩ : ∃ z : LReturnJets.Jet, LReturnJets.mul j225 j226=z := ⟨_,rfl⟩
  have j228_value : Bounds (4999999999999999999999999996946574051639/5000000000000000000000000000000000000000 : ℝ) j228.value (10000000000000000000000000006100724239817/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h774
  have j228_tangent : Bounds (613142110728969208424778776277854151841/1250000000000000000000000000000000000000 : ℝ) j228.tangent (4905136885831753667398230274180551222043/10000000000000000000000000000000000000000 : ℝ) := by
    simpa only [← hj228,LReturnJets.mul,LReturnJets.add,LReturnJets.neg,div_eq_mul_inv] using h777
  have he11 : jacobian c d 1 1=j228.tangent := by
    simp only [jacobian,shapeJet,hm13,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,LReturnJets.div]
    rw [← hj228,← hj226]
    rfl
  rw [he01,he11]
  exact ⟨enlarge j227_tangent (by norm_num) (by norm_num),
    enlarge j228_tangent (by norm_num) (by norm_num)⟩

theorem jacobian_bounds {c d : ℝ}
    (hc : Bounds (318481427627118630646451312501/1000000000000000000000000000000 : ℝ) c (39810178453389828830806414063/125000000000000000000000000000 : ℝ))
    (hd : Bounds (-205046423935149745096270174003/200000000000000000000000000000 : ℝ) d (-256308029918937181370337717503/250000000000000000000000000000 : ℝ)) :
    Bounds (222479725014657906929/200000000000000000000 : ℝ) (jacobian c d 0 0) (222479725014657906931/200000000000000000000 : ℝ) ∧
    Bounds (129194020546319545843/200000000000000000000 : ℝ) (jacobian c d 0 1) (25838804109263909169/40000000000000000000 : ℝ) ∧
    Bounds (30060062817099939949/40000000000000000000 : ℝ) (jacobian c d 1 0) (150300314085499699747/200000000000000000000 : ℝ) ∧
    Bounds (98102737716635073347/200000000000000000000 : ℝ) (jacobian c d 1 1) (98102737716635073349/200000000000000000000 : ℝ) := by
  constructor
  · convert (column_0_bounds hc hd).1 using 1 <;> norm_num
  constructor
  · convert (column_1_bounds hc hd).1 using 1 <;> norm_num
  constructor
  · convert (column_0_bounds hc hd).2 using 1 <;> norm_num
  · convert (column_1_bounds hc hd).2 using 1 <;> norm_num
end BfgsVerification.LShapeFineCertificate

