import BfgsVerification.AlgebraicSeedOrbitData
/-! Generated rational interval proof candidates for D's nine strict oracle decisions.
Every endpoint and implication is checked by Lean; Python is not trusted. -/
noncomputable section
namespace BfgsVerification.SeedOrbit
open IntervalBounds SeedCycle AlgebraicSeed

theorem tight_ratio {c d : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000)) :
    Bounds (6019/100000) (ratio c d) (6021/100000) := by
  have b0 : Bounds (129 : ℝ) (129 : ℝ) (129 : ℝ) := by
    convert IntervalBounds.exact (129 : ℝ) using 1 <;> norm_num
  have b2 : Bounds (8 : ℝ) (8 : ℝ) (8 : ℝ) := by
    convert IntervalBounds.exact (8 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (-1025233/125000 : ℝ) ((8 : ℝ)*d) (-128154/15625 : ℝ) := by
    convert IntervalBounds.mul_np b2 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b5 : Bounds (8520337/1000000 : ℝ) (c-((8 : ℝ)*d)) (4260173/500000 : ℝ) := by
    convert IntervalBounds.sub hc b4 using 1 <;> norm_num
  have b6 : Bounds (1099123473/1000000 : ℝ) ((129 : ℝ)*(c-((8 : ℝ)*d))) (549562317/500000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b5 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b7 : Bounds (16 : ℝ) (16 : ℝ) (16 : ℝ) := by
    convert IntervalBounds.exact (16 : ℝ) using 1 <;> norm_num
  have b8 : Bounds (318481/62500 : ℝ) ((16 : ℝ)*c) (159241/31250 : ℝ) := by
    convert IntervalBounds.mul_nn b7 hc (by norm_num) (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (127 : ℝ) (127 : ℝ) (127 : ℝ) := by
    convert IntervalBounds.exact (127 : ℝ) using 1 <;> norm_num
  have b10 : Bounds (-130204591/1000000 : ℝ) ((127 : ℝ)*d) (-8137779/62500 : ℝ) := by
    convert IntervalBounds.mul_np b9 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b11 : Bounds (422813/3125 : ℝ) (((16 : ℝ)*c)-((127 : ℝ)*d)) (135300303/1000000 : ℝ) := by
    convert IntervalBounds.sub b8 b10 using 1 <;> norm_num
  have b12 : Bounds (372813/3125 : ℝ) ((((16 : ℝ)*c)-((127 : ℝ)*d))-(16 : ℝ)) (119300303/1000000 : ℝ) := by
    convert IntervalBounds.sub b11 b7 using 1 <;> norm_num
  have b13 : Bounds (40447087/1000000 : ℝ) ((127 : ℝ)*c) (20223607/500000 : ℝ) := by
    convert IntervalBounds.mul_nn b9 hc (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (-1025233/62500 : ℝ) ((16 : ℝ)*d) (-256308/15625 : ℝ) := by
    convert IntervalBounds.mul_np b7 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (24043359/1000000 : ℝ) (((127 : ℝ)*c)+((16 : ℝ)*d)) (12021751/500000 : ℝ) := by
    convert IntervalBounds.add b13 b14 using 1 <;> norm_num
  have b16 : Bounds (153043359/1000000 : ℝ) ((((127 : ℝ)*c)+((16 : ℝ)*d))+(129 : ℝ)) (76521751/500000 : ℝ) := by
    convert IntervalBounds.add b15 b0 using 1 <;> norm_num
  have b17 : Bounds (57056553798867/3125000000 : ℝ) (((((16 : ℝ)*c)-((127 : ℝ)*d))-(16 : ℝ))*((((127 : ℝ)*c)+((16 : ℝ)*d))+(129 : ℝ))) (9129068080390553/500000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b12 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b18 : Bounds (500000000000/9129068080390553 : ℝ) ((((((16 : ℝ)*c)-((127 : ℝ)*d))-(16 : ℝ))*((((127 : ℝ)*c)+((16 : ℝ)*d))+(129 : ℝ))))⁻¹ (3125000000/57056553798867 : ℝ) := by
    convert IntervalBounds.inv_pos b17 (by norm_num) using 1 <;> norm_num
  have b19 : Bounds (549561736500000/9129068080390553 : ℝ) (((129 : ℝ)*(c-((8 : ℝ)*d)))*((((((16 : ℝ)*c)-((127 : ℝ)*d))-(16 : ℝ))*((((127 : ℝ)*c)+((16 : ℝ)*d))+(129 : ℝ))))⁻¹) (1144921493750/19018851266289 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b18 (by norm_num) (by norm_num) using 1 <;> norm_num
  have h := b19
  unfold Bounds at h ⊢
  dsimp only [ratio,R,V,U]
  simp only [div_eq_mul_inv]
  constructor <;> linarith only [h.1,h.2]

/-- Phase 0, trial α=0, unique branch 0; accepted base point. -/
theorem raw_base_0 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) ∧
    0 < (((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))) ∧
    0 < (((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ))))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b11 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (0 : ℝ) ((0 : ℝ)*(-1 : ℝ)) (0 : ℝ) := by
    convert IntervalBounds.mul_np b10 b11 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b13 : Bounds (27831410117/31327000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.add b9 b12 using 1 <;> norm_num
  have b14 : Bounds (27831410117/31327000000 : ℝ) ((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ)))) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b16 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b17 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b18 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b16 b17 using 1 <;> norm_num
  have b19 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b18 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b20 : Bounds (0 : ℝ) ((0 : ℝ)*(0 : ℝ)) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b10 b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b21 : Bounds (-7735427893/93979000000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ))) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.add b19 b20 using 1 <;> norm_num
  have b22 : Bounds (0 : ℝ) ((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b10 b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b23 : Bounds (27831410117/31327000000 : ℝ) (((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ))))) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.add b14 b22 using 1 <;> norm_num
  have b24 : Bounds (-5218474963/5873687500 : ℝ) ((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ)))) (-27831410117/31327000000 : ℝ) := by
    convert IntervalBounds.mul_pn b11 b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b25 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b26 : Bounds (483335713/46990500000 : ℝ) ((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))) (7735427893/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b25 b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (-3878076557009597/4416120199500000 : ℝ) (((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ))))) (-20682216981480333/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b24 b26 using 1 <;> norm_num
  have b28 : Bounds (41606761712564677/23552641064000000 : ℝ) ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) (7801576520991221/4416120199500000 : ℝ) := by
    convert IntervalBounds.sub b23 b27 using 1 <;> norm_num
  have b29 : Bounds (8863775325472277/31327000000000000 : ℝ) (c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ)))) (830995171583083/2936843750000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b30 : Bounds (10323567493967/122371093750000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))) (7930615945024069/93979000000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b31 : Bounds (11506608603927829/31327000000000000 : ℝ) ((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ))))) (1380898457427309/3759160000000000 : ℝ) := by
    convert IntervalBounds.add b29 b30 using 1 <;> norm_num
  have b32 : Bounds (61363317679596410957/117763205320000000000 : ℝ) ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) (1534287072665882558409/2944080133000000000000 : ℝ) := by
    convert IntervalBounds.sub b23 b31 using 1 <;> norm_num
  have b33 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b34 : Bounds (121812410117/31327000000 : ℝ) ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) (22839537463/5873687500 : ℝ) := by
    convert IntervalBounds.add b23 b33 using 1 <;> norm_num
  have b35 : Bounds (12402587537/5873687500 : ℝ) ((3 : ℝ)-(((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) (66149589883/31327000000 : ℝ) := by
    convert IntervalBounds.sub b33 b23 using 1 <;> norm_num
  have b36 : Bounds (9370284041490403/4416120199500000 : ℝ) ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) (49975706210519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b27 b33 using 1 <;> norm_num
  have b37 : Bounds (91340140173480333/23552641064000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) (17126437155509597/4416120199500000 : ℝ) := by
    convert IntervalBounds.sub b33 b27 using 1 <;> norm_num
  have b38 : Bounds (105487608603927829/31327000000000000 : ℝ) (((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) (12658378457427309/3759160000000000 : ℝ) := by
    convert IntervalBounds.add b31 b33 using 1 <;> norm_num
  have b39 : Bounds (9896581542572691/3759160000000000 : ℝ) ((3 : ℝ)-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))))) (82474391396072171/31327000000000000 : ℝ) := by
    convert IntervalBounds.sub b33 b31 using 1 <;> norm_num
  have b40 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b41 : Bounds (12230960713/5873812500 : ℝ) ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(0 : ℝ)))) (195693427893/93979000000 : ℝ) := by
    convert IntervalBounds.sub b40 b21 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (41606761712564677/23552641064000000 : ℝ)) b28.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (61363317679596410957/117763205320000000000 : ℝ)) b32.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (121812410117/31327000000 : ℝ)) b34.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (12402587537/5873687500 : ℝ)) b35.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (9370284041490403/4416120199500000 : ℝ)) b36.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (91340140173480333/23552641064000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (105487608603927829/31327000000000000 : ℝ)) b38.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (9896581542572691/3759160000000000 : ℝ)) b39.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (12230960713/5873812500 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (27831410117/31327000000 : ℝ)) b23.1⟩

/-- Phase 1, trial α=0, unique branch 1; accepted base point. -/
theorem raw_base_1 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))) ∧
    0 < (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ))))) := by
  have b0 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b3 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b5 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b3 hc using 1 <;> norm_num
  have b6 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b5 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b7 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b6 using 1 <;> norm_num
  have b8 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b3 hr using 1 <;> norm_num
  have b9 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b8 (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b7 b9 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b11 : Bounds (-3495589883/31327000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.sub b10 b3 using 1 <;> norm_num
  have b12 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (127/256 : ℝ) (127/256 : ℝ) (127/256 : ℝ) := by
    convert IntervalBounds.exact (127/256 : ℝ) using 1 <;> norm_num
  have b14 : Bounds (0 : ℝ) ((0 : ℝ)*(127/256 : ℝ)) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b12 b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (-3495589883/31327000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.add b11 b14 using 1 <;> norm_num
  have b16 : Bounds (655212537/5873687500 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ)))) (3495589883/31327000000 : ℝ) := by
    convert IntervalBounds.mul_pp b0 b15 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b17 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b19 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b20 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b21 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b19 b20 using 1 <;> norm_num
  have b22 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b21 b9 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b23 : Bounds (1/16 : ℝ) (1/16 : ℝ) (1/16 : ℝ) := by
    convert IntervalBounds.exact (1/16 : ℝ) using 1 <;> norm_num
  have b24 : Bounds (0 : ℝ) ((0 : ℝ)*(1/16 : ℝ)) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b12 b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b25 : Bounds (-7735427893/93979000000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ))) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.add b22 b24 using 1 <;> norm_num
  have b26 : Bounds (483335713/46990500000 : ℝ) ((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))) (7735427893/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b17 b25 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (538043642490403/4416120199500000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ))))) (2870424082519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b16 b26 using 1 <;> norm_num
  have b28 : Bounds (-3495589883/31327000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ)))) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.mul_np b3 b15 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b29 : Bounds (0 : ℝ) ((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b12 b25 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b30 : Bounds (-3495589883/31327000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ))))) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.add b28 b29 using 1 <;> norm_num
  have b31 : Bounds (1030663878008779/4416120199500000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) (5498520415435323/23552641064000000 : ℝ) := by
    convert IntervalBounds.sub b27 b30 using 1 <;> norm_num
  have b32 : Bounds (-556641228558803/15663500000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ)))) (-208672743996297/5873687500000000 : ℝ) := by
    convert IntervalBounds.mul_np hc b15 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b33 : Bounds (10323567493967/122371093750000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))) (7930615945024069/93979000000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b25 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b34 : Bounds (764775410668973/15663500000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ))))) (4591852041083317/93979000000000000 : ℝ) := by
    convert IntervalBounds.add b32 b33 using 1 <;> norm_num
  have b35 : Bounds (644540438307754785023/8832240399000000000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) (107528676838219773933/1472040066500000000000 : ℝ) := by
    convert IntervalBounds.sub b27 b34 using 1 <;> norm_num
  have b36 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b37 : Bounds (90485410117/31327000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (16965849963/5873687500 : ℝ) := by
    convert IntervalBounds.add b30 b36 using 1 <;> norm_num
  have b38 : Bounds (18276275037/5873687500 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) (97476589883/31327000000 : ℝ) := by
    convert IntervalBounds.sub b36 b30 using 1 <;> norm_num
  have b39 : Bounds (13786404240990403/4416120199500000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (73528347274519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b27 b36 using 1 <;> norm_num
  have b40 : Bounds (67787499109480333/23552641064000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) (12710316956009597/4416120199500000 : ℝ) := by
    convert IntervalBounds.sub b36 b27 using 1 <;> norm_num
  have b41 : Bounds (47755275410668973/15663500000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (286528852041083317/93979000000000000 : ℝ) := by
    convert IntervalBounds.add b34 b36 using 1 <;> norm_num
  have b42 : Bounds (277345147958916683/93979000000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((0 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))))) (46225724589331027/15663500000000000 : ℝ) := by
    convert IntervalBounds.sub b36 b34 using 1 <;> norm_num
  have b43 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b44 : Bounds (12230960713/5873812500 : ℝ) ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((0 : ℝ)*(1/16 : ℝ)))) (195693427893/93979000000 : ℝ) := by
    convert IntervalBounds.sub b43 b25 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1030663878008779/4416120199500000 : ℝ)) b31.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (644540438307754785023/8832240399000000000000 : ℝ)) b35.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (90485410117/31327000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (18276275037/5873687500 : ℝ)) b38.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (13786404240990403/4416120199500000 : ℝ)) b39.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (67787499109480333/23552641064000000 : ℝ)) b40.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (47755275410668973/15663500000000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (277345147958916683/93979000000000000 : ℝ)) b42.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (12230960713/5873812500 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (538043642490403/4416120199500000 : ℝ)) b27.1⟩

/-- Phase 2, trial α=0, unique branch 2; accepted base point. -/
theorem raw_base_2 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))) ∧
    0 < ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d))))) := by
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b3 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b3 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b3 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (6235077497/501232000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.sub b9 b1 using 1 <;> norm_num
  have b11 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (16 : ℝ) (16 : ℝ) (16 : ℝ) := by
    convert IntervalBounds.exact (16 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (6019/6250 : ℝ) ((16 : ℝ)*r) (6021/6250 : ℝ) := by
    convert IntervalBounds.mul_nn b12 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (2051028421/3125000000 : ℝ) (((16 : ℝ)*r)*((1 : ℝ)-c)) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b13 b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (0 : ℝ) ((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b16 : Bounds (6235077497/501232000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.add b10 b15 using 1 <;> norm_num
  have b17 : Bounds (1985753716322057/501232000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (2986591811472373/751832000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b19 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b20 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b21 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b19 b20 using 1 <;> norm_num
  have b22 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b21 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b23 : Bounds (-3133503009/46989500000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b22 b20 using 1 <;> norm_num
  have b24 : Bounds (-16 : ℝ) (-16 : ℝ) (-16 : ℝ) := by
    convert IntervalBounds.exact (-16 : ℝ) using 1 <;> norm_num
  have b25 : Bounds (-6021/6250 : ℝ) ((-16 : ℝ)*r) (-6019/6250 : ℝ) := by
    convert IntervalBounds.mul_pn b24 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b26 : Bounds (385679463/390625000 : ℝ) (((-16 : ℝ)*r)*d) (6172927893/6250000000 : ℝ) := by
    convert IntervalBounds.mul_pp b25 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (0 : ℝ) ((0 : ℝ)*(((-16 : ℝ)*r)*d)) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b26 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b28 : Bounds (-3133503009/46989500000 : ℝ) (((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d))) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b23 b27 using 1 <;> norm_num
  have b29 : Bounds (133812389606597/1957937500000000 : ℝ) (d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))) (3212570690426097/46989500000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b28 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b30 : Bounds (36241725455610889/501232000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d))))) (2175508914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b17 b29 using 1 <;> norm_num
  have b31 : Bounds (6235077497/501232000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.mul_nn b3 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b32 : Bounds (0 : ℝ) ((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b11 b28 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b33 : Bounds (6235077497/501232000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d))))) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.add b31 b32 using 1 <;> norm_num
  have b34 : Bounds (2818417948200324737331/47105282128000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) (56432840797454679219/942105642560000000000 : ℝ) := by
    convert IntervalBounds.sub b30 b33 using 1 <;> norm_num
  have b35 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b36 : Bounds (-18755168653/1503664000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (-6235077497/501232000000 : ℝ) := by
    convert IntervalBounds.mul_pn b35 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b37 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b38 : Bounds (6264918283/751848000000 : ℝ) ((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))) (3133503009/375916000000 : ℝ) := by
    convert IntervalBounds.mul_pp b37 b28 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b39 : Bounds (-585087994541479/141315846384000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d))))) (-193313353038791/47105282128000000 : ℝ) := by
    convert IntervalBounds.add b36 b38 using 1 <;> norm_num
  have b40 : Bounds (3599274469631646737331/47105282128000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) (216158263168627397657/2826316927680000000000 : ℝ) := by
    convert IntervalBounds.sub b30 b39 using 1 <;> norm_num
  have b41 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b42 : Bounds (1509931077497/501232000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (4529747168653/1503664000000 : ℝ) := by
    convert IntervalBounds.add b33 b41 using 1 <;> norm_num
  have b43 : Bounds (4492236831347/1503664000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) (1497460922503/501232000000 : ℝ) := by
    convert IntervalBounds.sub b41 b33 using 1 <;> norm_num
  have b44 : Bounds (423362451157458521/141315846384000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (141122533030961209/47105282128000000 : ℝ) := by
    convert IntervalBounds.add b39 b41 using 1 <;> norm_num
  have b45 : Bounds (141509159737038791/47105282128000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) (424532627146541479/141315846384000000 : ℝ) := by
    convert IntervalBounds.sub b41 b39 using 1 <;> norm_num
  have b46 : Bounds (1539937725455610889/501232000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (92395348914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b30 b41 using 1 <;> norm_num
  have b47 : Bounds (88044331085668403/30073280000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((0 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))))) (1467454274544389111/501232000000000000 : ℝ) := by
    convert IntervalBounds.sub b41 b30 using 1 <;> norm_num
  have b48 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b49 : Bounds (194226918283/93981000000 : ℝ) ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))) (97112503009/46989500000 : ℝ) := by
    convert IntervalBounds.sub b48 b28 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2818417948200324737331/47105282128000000000000 : ℝ)) b34.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3599274469631646737331/47105282128000000000000 : ℝ)) b40.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1509931077497/501232000000 : ℝ)) b42.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4492236831347/1503664000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (423362451157458521/141315846384000000 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (141509159737038791/47105282128000000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1539937725455610889/501232000000000000 : ℝ)) b46.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (88044331085668403/30073280000000000 : ℝ)) b47.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (194226918283/93981000000 : ℝ)) b49.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (36241725455610889/501232000000000000 : ℝ)) b30.1⟩

/-- Phase 0, trial α=1, unique branch 1; accept. -/
theorem raw_trial_0 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))-(((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) ∧
    0 < (((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) ∧
    0 < ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))) ∧
    0 < (((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ))))) ∧
    0 < (((((1 : ℝ)*(((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹))+((0 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))+((1/3 : ℝ)*((1 : ℝ)*(((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ))))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) ∧
    0 < (-((1 : ℝ)*(((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ))))) ∧
    0 < ((1 : ℝ)*(((-1 : ℝ)*(-1 : ℝ))+((-1/8 : ℝ)*(0 : ℝ)))) := by
  have b0 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b3 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b5 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b3 hc using 1 <;> norm_num
  have b6 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b5 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b7 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b6 using 1 <;> norm_num
  have b8 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b3 hr using 1 <;> norm_num
  have b9 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b8 (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b7 b9 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b11 : Bounds (-1 : ℝ) ((1 : ℝ)*(-1 : ℝ)) (-1 : ℝ) := by
    convert IntervalBounds.mul_np b3 b0 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b12 : Bounds (-3495589883/31327000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.add b10 b11 using 1 <;> norm_num
  have b13 : Bounds (655212537/5873687500 : ℝ) ((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ)))) (3495589883/31327000000 : ℝ) := by
    convert IntervalBounds.mul_pp b0 b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b16 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b17 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b18 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b16 b17 using 1 <;> norm_num
  have b19 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b18 b9 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b20 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b21 : Bounds (0 : ℝ) ((1 : ℝ)*(0 : ℝ)) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b3 b20 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b22 : Bounds (-7735427893/93979000000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ))) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.add b19 b21 using 1 <;> norm_num
  have b23 : Bounds (483335713/46990500000 : ℝ) ((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))) (7735427893/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b14 b22 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b24 : Bounds (538043642490403/4416120199500000 : ℝ) (((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ))))) (2870424082519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b13 b23 using 1 <;> norm_num
  have b25 : Bounds (-3495589883/31327000000 : ℝ) ((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ)))) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.mul_np b3 b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b26 : Bounds (0 : ℝ) ((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b20 b22 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (-3495589883/31327000000 : ℝ) (((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ))))) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.add b25 b26 using 1 <;> norm_num
  have b28 : Bounds (1030663878008779/4416120199500000 : ℝ) ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))-(((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) (5498520415435323/23552641064000000 : ℝ) := by
    convert IntervalBounds.sub b24 b27 using 1 <;> norm_num
  have b29 : Bounds (-556641228558803/15663500000000000 : ℝ) (c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ)))) (-208672743996297/5873687500000000 : ℝ) := by
    convert IntervalBounds.mul_np hc b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b30 : Bounds (10323567493967/122371093750000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))) (7930615945024069/93979000000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b22 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b31 : Bounds (764775410668973/15663500000000000 : ℝ) ((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ))))) (4591852041083317/93979000000000000 : ℝ) := by
    convert IntervalBounds.add b29 b30 using 1 <;> norm_num
  have b32 : Bounds (644540438307754785023/8832240399000000000000 : ℝ) ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) (107528676838219773933/1472040066500000000000 : ℝ) := by
    convert IntervalBounds.sub b24 b31 using 1 <;> norm_num
  have b33 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b34 : Bounds (90485410117/31327000000 : ℝ) ((((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) (16965849963/5873687500 : ℝ) := by
    convert IntervalBounds.add b27 b33 using 1 <;> norm_num
  have b35 : Bounds (18276275037/5873687500 : ℝ) ((3 : ℝ)-(((1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) (97476589883/31327000000 : ℝ) := by
    convert IntervalBounds.sub b33 b27 using 1 <;> norm_num
  have b36 : Bounds (13786404240990403/4416120199500000 : ℝ) ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) (73528347274519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b24 b33 using 1 <;> norm_num
  have b37 : Bounds (67787499109480333/23552641064000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) (12710316956009597/4416120199500000 : ℝ) := by
    convert IntervalBounds.sub b33 b24 using 1 <;> norm_num
  have b38 : Bounds (47755275410668973/15663500000000000 : ℝ) (((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))+(3 : ℝ)) (286528852041083317/93979000000000000 : ℝ) := by
    convert IntervalBounds.add b31 b33 using 1 <;> norm_num
  have b39 : Bounds (277345147958916683/93979000000000000 : ℝ) ((3 : ℝ)-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) (46225724589331027/15663500000000000 : ℝ) := by
    convert IntervalBounds.sub b33 b31 using 1 <;> norm_num
  have b40 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b41 : Bounds (12230960713/5873812500 : ℝ) ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))) (195693427893/93979000000 : ℝ) := by
    convert IntervalBounds.sub b40 b22 using 1 <;> norm_num
  have b42 : Bounds (27831410117/31327000000 : ℝ) ((1 : ℝ)*(((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b3 b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b43 : Bounds (0 : ℝ) ((0 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)) (0 : ℝ) := by
    convert IntervalBounds.mul_np b20 b19 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b44 : Bounds (27831410117/31327000000 : ℝ) (((1 : ℝ)*(((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹))+((0 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹))) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.add b42 b43 using 1 <;> norm_num
  have b45 : Bounds (1/3 : ℝ) (1/3 : ℝ) (1/3 : ℝ) := by
    convert IntervalBounds.exact (1/3 : ℝ) using 1 <;> norm_num
  have b46 : Bounds (0 : ℝ) ((0 : ℝ)*(0 : ℝ)) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b20 b20 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b47 : Bounds (-1 : ℝ) (((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ))) (-1 : ℝ) := by
    convert IntervalBounds.add b11 b46 using 1 <;> norm_num
  have b48 : Bounds (-1 : ℝ) ((1 : ℝ)*(((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ)))) (-1 : ℝ) := by
    convert IntervalBounds.mul_np b3 b47 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b49 : Bounds (-1/3 : ℝ) ((1/3 : ℝ)*((1 : ℝ)*(((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ))))) (-1/3 : ℝ) := by
    convert IntervalBounds.mul_np b45 b48 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b50 : Bounds (52167230351/93981000000 : ℝ) ((((1 : ℝ)*(((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹))+((0 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))+((1/3 : ℝ)*((1 : ℝ)*(((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ)))))) (9781737389/17621062500 : ℝ) := by
    convert IntervalBounds.add b44 b49 using 1 <;> norm_num
  have b51 : Bounds (30609720881694031/70657923192000000 : ℝ) (((((1 : ℝ)*(((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹))+((0 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))+((1/3 : ℝ)*((1 : ℝ)*(((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ))))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(-1 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(0 : ℝ)))))) (637805418330407/1472040066500000 : ℝ) := by
    convert IntervalBounds.sub b50 b24 using 1 <;> norm_num
  have b52 : Bounds (1 : ℝ) (-((1 : ℝ)*(((1 : ℝ)*(-1 : ℝ))+((0 : ℝ)*(0 : ℝ))))) (1 : ℝ) := by
    convert IntervalBounds.neg b48 using 1 <;> norm_num
  have b53 : Bounds (1 : ℝ) ((-1 : ℝ)*(-1 : ℝ)) (1 : ℝ) := by
    convert IntervalBounds.mul_pp b0 b0 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b54 : Bounds (0 : ℝ) ((-1/8 : ℝ)*(0 : ℝ)) (0 : ℝ) := by
    convert IntervalBounds.mul_pn b14 b20 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b55 : Bounds (1 : ℝ) (((-1 : ℝ)*(-1 : ℝ))+((-1/8 : ℝ)*(0 : ℝ))) (1 : ℝ) := by
    convert IntervalBounds.add b53 b54 using 1 <;> norm_num
  have b56 : Bounds (1 : ℝ) ((1 : ℝ)*(((-1 : ℝ)*(-1 : ℝ))+((-1/8 : ℝ)*(0 : ℝ)))) (1 : ℝ) := by
    convert IntervalBounds.mul_nn b3 b55 (by norm_num) (by norm_num) using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1030663878008779/4416120199500000 : ℝ)) b28.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (644540438307754785023/8832240399000000000000 : ℝ)) b32.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (90485410117/31327000000 : ℝ)) b34.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (18276275037/5873687500 : ℝ)) b35.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (13786404240990403/4416120199500000 : ℝ)) b36.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (67787499109480333/23552641064000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (47755275410668973/15663500000000000 : ℝ)) b38.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (277345147958916683/93979000000000000 : ℝ)) b39.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (12230960713/5873812500 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (538043642490403/4416120199500000 : ℝ)) b24.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (30609720881694031/70657923192000000 : ℝ)) b51.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) b52.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) b56.1⟩

/-- Phase 1, trial α=1, unique branch 0; reject by strict increase. -/
theorem raw_trial_1 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))) ∧
    0 < (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))) ∧
    0 < (-((1 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (-3495589883/31327000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.sub b9 b0 using 1 <;> norm_num
  have b11 : Bounds (127/256 : ℝ) (127/256 : ℝ) (127/256 : ℝ) := by
    convert IntervalBounds.exact (127/256 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (127/256 : ℝ) ((1 : ℝ)*(127/256 : ℝ)) (127/256 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b11 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b13 : Bounds (48182156093/125308000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))) (144555975757/375916000000 : ℝ) := by
    convert IntervalBounds.add b10 b12 using 1 <;> norm_num
  have b14 : Bounds (48182156093/125308000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ)))) (144555975757/375916000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b17 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b18 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b19 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b17 b18 using 1 <;> norm_num
  have b20 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b19 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b21 : Bounds (1/16 : ℝ) (1/16 : ℝ) (1/16 : ℝ) := by
    convert IntervalBounds.exact (1/16 : ℝ) using 1 <;> norm_num
  have b22 : Bounds (1/16 : ℝ) ((1 : ℝ)*(1/16 : ℝ)) (1/16 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b23 : Bounds (-1861740393/93979000000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ))) (-464889727/23495250000 : ℝ) := by
    convert IntervalBounds.add b20 b22 using 1 <;> norm_num
  have b24 : Bounds (0 : ℝ) ((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b15 b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b25 : Bounds (48182156093/125308000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ))))) (144555975757/375916000000 : ℝ) := by
    convert IntervalBounds.add b14 b24 using 1 <;> norm_num
  have b26 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b27 : Bounds (-144555975757/375916000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ)))) (-48182156093/125308000000 : ℝ) := by
    convert IntervalBounds.mul_pn b26 b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b28 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b29 : Bounds (464889727/187962000000 : ℝ) ((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))) (1861740393/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b28 b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b30 : Bounds (-13498135414311151/35328961596000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ))))) (-8997898953636583/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b27 b29 using 1 <;> norm_num
  have b31 : Bounds (18054120648564677/23552641064000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) (3385456321491221/4416120199500000 : ℝ) := by
    convert IntervalBounds.sub b25 b30 using 1 <;> norm_num
  have b32 : Bounds (15345101254654733/125308000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ)))) (23019238135520437/187958000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b33 : Bounds (9929579678993/489484375000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))) (1908717688336569/93979000000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b34 : Bounds (17887073652476941/125308000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ))))) (1073466940487743/7518320000000000 : ℝ) := by
    convert IntervalBounds.add b32 b33 using 1 <;> norm_num
  have b35 : Bounds (56933718104621415039/235526410640000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) (2847495757753408561761/11776320532000000000000 : ℝ) := by
    convert IntervalBounds.sub b25 b34 using 1 <;> norm_num
  have b36 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b37 : Bounds (424106156093/125308000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (1272303975757/375916000000 : ℝ) := by
    convert IntervalBounds.add b25 b36 using 1 <;> norm_num
  have b38 : Bounds (983192024243/375916000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) (327741843907/125308000000 : ℝ) := by
    convert IntervalBounds.sub b36 b25 using 1 <;> norm_num
  have b39 : Bounds (92488749373688849/35328961596000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (61660024238363417/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b30 b36 using 1 <;> norm_num
  have b40 : Bounds (79655822145636583/23552641064000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) (119485020202311151/35328961596000000 : ℝ) := by
    convert IntervalBounds.sub b36 b30 using 1 <;> norm_num
  have b41 : Bounds (393811073652476941/125308000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (23628426940487743/7518320000000000 : ℝ) := by
    convert IntervalBounds.add b34 b36 using 1 <;> norm_num
  have b42 : Bounds (21481493059512257/7518320000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))) (358036926347523059/125308000000000000 : ℝ) := by
    convert IntervalBounds.sub b36 b34 using 1 <;> norm_num
  have b43 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b44 : Bounds (47455389727/23495250000 : ℝ) ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))) (189819740393/93979000000 : ℝ) := by
    convert IntervalBounds.sub b43 b23 using 1 <;> norm_num
  have b45 : Bounds (655212537/5873687500 : ℝ) ((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))) (3495589883/31327000000 : ℝ) := by
    convert IntervalBounds.mul_pp b26 b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b46 : Bounds (483335713/46990500000 : ℝ) ((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)) (7735427893/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b28 b20 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b47 : Bounds (538043642490403/4416120199500000 : ℝ) (((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹))) (2870424082519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b45 b46 using 1 <;> norm_num
  have b48 : Bounds (6185797612408427/23552641064000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))) (9281166017695393/35328961596000000 : ℝ) := by
    convert IntervalBounds.sub b25 b47 using 1 <;> norm_num
  have b49 : Bounds (-127/256 : ℝ) ((-1 : ℝ)*(127/256 : ℝ)) (-127/256 : ℝ) := by
    convert IntervalBounds.mul_pn b26 b11 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b50 : Bounds (-1/128 : ℝ) ((-1/8 : ℝ)*(1/16 : ℝ)) (-1/128 : ℝ) := by
    convert IntervalBounds.mul_pn b28 b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b51 : Bounds (-129/256 : ℝ) (((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))) (-129/256 : ℝ) := by
    convert IntervalBounds.add b49 b50 using 1 <;> norm_num
  have b52 : Bounds (-129/256 : ℝ) ((1 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ)))) (-129/256 : ℝ) := by
    convert IntervalBounds.mul_np b0 b51 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b53 : Bounds (129/256 : ℝ) (-((1 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))) (129/256 : ℝ) := by
    convert IntervalBounds.neg b52 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (18054120648564677/23552641064000000 : ℝ)) b31.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (56933718104621415039/235526410640000000000 : ℝ)) b35.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (424106156093/125308000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (983192024243/375916000000 : ℝ)) b38.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (92488749373688849/35328961596000000 : ℝ)) b39.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (79655822145636583/23552641064000000 : ℝ)) b40.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (393811073652476941/125308000000000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (21481493059512257/7518320000000000 : ℝ)) b42.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (47455389727/23495250000 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (48182156093/125308000000 : ℝ)) b25.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (6185797612408427/23552641064000000 : ℝ)) b48.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (129/256 : ℝ)) b53.1⟩

/-- Phase 1, trial α=1/2, unique branch 0; reject by strict increase. -/
theorem raw_trial_2 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))) ∧
    0 < (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))) ∧
    0 < (-((1/2 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (-3495589883/31327000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.sub b9 b0 using 1 <;> norm_num
  have b11 : Bounds (1/2 : ℝ) (1/2 : ℝ) (1/2 : ℝ) := by
    convert IntervalBounds.exact (1/2 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (127/256 : ℝ) (127/256 : ℝ) (127/256 : ℝ) := by
    convert IntervalBounds.exact (127/256 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (127/512 : ℝ) ((1/2 : ℝ)*(127/256 : ℝ)) (127/512 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (34199796561/250616000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))) (102622373389/751832000000 : ℝ) := by
    convert IntervalBounds.add b10 b13 using 1 <;> norm_num
  have b15 : Bounds (34199796561/250616000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ)))) (102622373389/751832000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b16 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b18 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b19 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b20 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b18 b19 using 1 <;> norm_num
  have b21 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b20 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b22 : Bounds (1/16 : ℝ) (1/16 : ℝ) (1/16 : ℝ) := by
    convert IntervalBounds.exact (1/16 : ℝ) using 1 <;> norm_num
  have b23 : Bounds (1/32 : ℝ) ((1/2 : ℝ)*(1/16 : ℝ)) (1/32 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b22 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b24 : Bounds (-4798584143/93979000000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ))) (-2398232579/46990500000 : ℝ) := by
    convert IntervalBounds.add b21 b23 using 1 <;> norm_num
  have b25 : Bounds (0 : ℝ) ((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b16 b24 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b26 : Bounds (34199796561/250616000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ))))) (102622373389/751832000000 : ℝ) := by
    convert IntervalBounds.add b15 b25 using 1 <;> norm_num
  have b27 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b28 : Bounds (-102622373389/751832000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ)))) (-34199796561/250616000000 : ℝ) := by
    convert IntervalBounds.mul_pn b27 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b29 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b30 : Bounds (2398232579/375924000000 : ℝ) ((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))) (4798584143/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b29 b24 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b31 : Bounds (-9193786274387927/70657923192000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ))))) (-1531868717779229/11776320532000000 : ℝ) := by
    convert IntervalBounds.add b28 b30 using 1 <;> norm_num
  have b32 : Bounds (6277800116564677/23552641064000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) (1177396221741221/4416120199500000 : ℝ) := by
    convert IntervalBounds.sub b26 b31 using 1 <;> norm_num
  have b33 : Bounds (10891985408543841/250616000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ)))) (16341689360837749/375916000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b34 : Bounds (51223849654861/978968750000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))) (4919666816680319/93979000000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b24 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b35 : Bounds (24005290920188257/250616000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ))))) (1440814265102361/15036640000000000 : ℝ) := by
    convert IntervalBounds.add b33 b34 using 1 <;> norm_num
  have b36 : Bounds (19144865137262716953/471052821280000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) (958857855768830795397/23552641064000000000000 : ℝ) := by
    convert IntervalBounds.sub b26 b35 using 1 <;> norm_num
  have b37 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b38 : Bounds (786047796561/250616000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (2358118373389/751832000000 : ℝ) := by
    convert IntervalBounds.add b26 b37 using 1 <;> norm_num
  have b39 : Bounds (2152873626611/751832000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) (717648203439/250616000000 : ℝ) := by
    convert IntervalBounds.sub b37 b26 using 1 <;> norm_num
  have b40 : Bounds (202779983301612073/70657923192000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (33797092878220771/11776320532000000 : ℝ) := by
    convert IntervalBounds.add b31 b37 using 1 <;> norm_num
  have b41 : Bounds (36860830313779229/11776320532000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) (221167555850387927/70657923192000000 : ℝ) := by
    convert IntervalBounds.sub b37 b31 using 1 <;> norm_num
  have b42 : Bounds (775853290920188257/250616000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (46550734265102361/15036640000000000 : ℝ) := by
    convert IntervalBounds.add b35 b37 using 1 <;> norm_num
  have b43 : Bounds (43669105734897639/15036640000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))) (727842709079811743/250616000000000000 : ℝ) := by
    convert IntervalBounds.sub b37 b35 using 1 <;> norm_num
  have b44 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b45 : Bounds (96379232579/46990500000 : ℝ) ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))) (192756584143/93979000000 : ℝ) := by
    convert IntervalBounds.sub b44 b24 using 1 <;> norm_num
  have b46 : Bounds (655212537/5873687500 : ℝ) ((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))) (3495589883/31327000000 : ℝ) := by
    convert IntervalBounds.mul_pp b27 b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b47 : Bounds (483335713/46990500000 : ℝ) ((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)) (7735427893/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b29 b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b48 : Bounds (538043642490403/4416120199500000 : ℝ) (((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹))) (2870424082519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b46 b47 using 1 <;> norm_num
  have b49 : Bounds (42954824810819/2944080133000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/2 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/2 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))) (1035854993625161/70657923192000000 : ℝ) := by
    convert IntervalBounds.sub b26 b48 using 1 <;> norm_num
  have b50 : Bounds (-127/256 : ℝ) ((-1 : ℝ)*(127/256 : ℝ)) (-127/256 : ℝ) := by
    convert IntervalBounds.mul_pn b27 b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b51 : Bounds (-1/128 : ℝ) ((-1/8 : ℝ)*(1/16 : ℝ)) (-1/128 : ℝ) := by
    convert IntervalBounds.mul_pn b29 b22 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b52 : Bounds (-129/256 : ℝ) (((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))) (-129/256 : ℝ) := by
    convert IntervalBounds.add b50 b51 using 1 <;> norm_num
  have b53 : Bounds (-129/512 : ℝ) ((1/2 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ)))) (-129/512 : ℝ) := by
    convert IntervalBounds.mul_np b11 b52 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b54 : Bounds (129/512 : ℝ) (-((1/2 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))) (129/512 : ℝ) := by
    convert IntervalBounds.neg b53 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (6277800116564677/23552641064000000 : ℝ)) b32.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (19144865137262716953/471052821280000000000 : ℝ)) b36.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (786047796561/250616000000 : ℝ)) b38.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2152873626611/751832000000 : ℝ)) b39.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (202779983301612073/70657923192000000 : ℝ)) b40.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (36860830313779229/11776320532000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (775853290920188257/250616000000000000 : ℝ)) b42.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (43669105734897639/15036640000000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (96379232579/46990500000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (34199796561/250616000000 : ℝ)) b26.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (42954824810819/2944080133000000 : ℝ)) b49.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (129/512 : ℝ)) b54.1⟩

/-- Phase 1, trial α=1/4, unique branch 2; accept. -/
theorem raw_trial_3 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))) ∧
    0 < ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ))))) ∧
    0 < (((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))+((1/3 : ℝ)*((1/4 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) ∧
    0 < (-((1/4 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))) ∧
    0 < ((1/4 : ℝ)*((c*(127/256 : ℝ))+(d*(1/16 : ℝ)))) := by
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b3 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b3 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b3 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (-3495589883/31327000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)) (-655212537/5873687500 : ℝ) := by
    convert IntervalBounds.sub b9 b3 using 1 <;> norm_num
  have b11 : Bounds (1/4 : ℝ) (1/4 : ℝ) (1/4 : ℝ) := by
    convert IntervalBounds.exact (1/4 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (127/256 : ℝ) (127/256 : ℝ) (127/256 : ℝ) := by
    convert IntervalBounds.exact (127/256 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (127/1024 : ℝ) ((1/4 : ℝ)*(127/256 : ℝ)) (127/1024 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (6235077497/501232000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.add b10 b13 using 1 <;> norm_num
  have b15 : Bounds (1985753716322057/501232000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ)))) (2986591811472373/751832000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b17 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b18 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b19 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b17 b18 using 1 <;> norm_num
  have b20 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b19 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b21 : Bounds (1/16 : ℝ) (1/16 : ℝ) (1/16 : ℝ) := by
    convert IntervalBounds.exact (1/16 : ℝ) using 1 <;> norm_num
  have b22 : Bounds (1/64 : ℝ) ((1/4 : ℝ)*(1/16 : ℝ)) (1/64 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b23 : Bounds (-3133503009/46989500000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ))) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b20 b22 using 1 <;> norm_num
  have b24 : Bounds (133812389606597/1957937500000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))) (3212570690426097/46989500000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b25 : Bounds (36241725455610889/501232000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ))))) (2175508914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b15 b24 using 1 <;> norm_num
  have b26 : Bounds (6235077497/501232000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ)))) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.mul_nn b3 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b28 : Bounds (0 : ℝ) ((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b27 b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b29 : Bounds (6235077497/501232000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ))))) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.add b26 b28 using 1 <;> norm_num
  have b30 : Bounds (2818417948200324737331/47105282128000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) (56432840797454679219/942105642560000000000 : ℝ) := by
    convert IntervalBounds.sub b25 b29 using 1 <;> norm_num
  have b31 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b32 : Bounds (-18755168653/1503664000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ)))) (-6235077497/501232000000 : ℝ) := by
    convert IntervalBounds.mul_pn b31 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b33 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b34 : Bounds (6264918283/751848000000 : ℝ) ((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))) (3133503009/375916000000 : ℝ) := by
    convert IntervalBounds.mul_pp b33 b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b35 : Bounds (-585087994541479/141315846384000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ))))) (-193313353038791/47105282128000000 : ℝ) := by
    convert IntervalBounds.add b32 b34 using 1 <;> norm_num
  have b36 : Bounds (3599274469631646737331/47105282128000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) (216158263168627397657/2826316927680000000000 : ℝ) := by
    convert IntervalBounds.sub b25 b35 using 1 <;> norm_num
  have b37 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b38 : Bounds (1509931077497/501232000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (4529747168653/1503664000000 : ℝ) := by
    convert IntervalBounds.add b29 b37 using 1 <;> norm_num
  have b39 : Bounds (4492236831347/1503664000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((0 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) (1497460922503/501232000000 : ℝ) := by
    convert IntervalBounds.sub b37 b29 using 1 <;> norm_num
  have b40 : Bounds (423362451157458521/141315846384000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (141122533030961209/47105282128000000 : ℝ) := by
    convert IntervalBounds.add b35 b37 using 1 <;> norm_num
  have b41 : Bounds (141509159737038791/47105282128000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+((-1/8 : ℝ)*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) (424532627146541479/141315846384000000 : ℝ) := by
    convert IntervalBounds.sub b37 b35 using 1 <;> norm_num
  have b42 : Bounds (1539937725455610889/501232000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))+(3 : ℝ)) (92395348914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b25 b37 using 1 <;> norm_num
  have b43 : Bounds (88044331085668403/30073280000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) (1467454274544389111/501232000000000000 : ℝ) := by
    convert IntervalBounds.sub b37 b25 using 1 <;> norm_num
  have b44 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b45 : Bounds (194226918283/93981000000 : ℝ) ((2 : ℝ)-((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))) (97112503009/46989500000 : ℝ) := by
    convert IntervalBounds.sub b44 b23 using 1 <;> norm_num
  have b46 : Bounds (655212537/5873687500 : ℝ) ((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))) (3495589883/31327000000 : ℝ) := by
    convert IntervalBounds.mul_pp b31 b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b47 : Bounds (483335713/46990500000 : ℝ) ((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)) (7735427893/751832000000 : ℝ) := by
    convert IntervalBounds.mul_pp b33 b20 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b48 : Bounds (538043642490403/4416120199500000 : ℝ) (((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹))) (2870424082519667/23552641064000000 : ℝ) := by
    convert IntervalBounds.add b46 b47 using 1 <;> norm_num
  have b49 : Bounds (1/3 : ℝ) (1/3 : ℝ) (1/3 : ℝ) := by
    convert IntervalBounds.exact (1/3 : ℝ) using 1 <;> norm_num
  have b50 : Bounds (-127/256 : ℝ) ((-1 : ℝ)*(127/256 : ℝ)) (-127/256 : ℝ) := by
    convert IntervalBounds.mul_pn b31 b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b51 : Bounds (-1/128 : ℝ) ((-1/8 : ℝ)*(1/16 : ℝ)) (-1/128 : ℝ) := by
    convert IntervalBounds.mul_pn b33 b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b52 : Bounds (-129/256 : ℝ) (((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))) (-129/256 : ℝ) := by
    convert IntervalBounds.add b50 b51 using 1 <;> norm_num
  have b53 : Bounds (-129/1024 : ℝ) ((1/4 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ)))) (-129/1024 : ℝ) := by
    convert IntervalBounds.mul_np b11 b52 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b54 : Bounds (-43/1024 : ℝ) ((1/3 : ℝ)*((1/4 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))) (-43/1024 : ℝ) := by
    convert IntervalBounds.mul_np b49 b53 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b55 : Bounds (11283235041614771/141315846384000000 : ℝ) ((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))+((1/3 : ℝ)*((1/4 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ)))))) (3762794325679959/47105282128000000 : ℝ) := by
    convert IntervalBounds.add b48 b54 using 1 <;> norm_num
  have b56 : Bounds (21208197554497602343/2826316927680000000000 : ℝ) (((((-1 : ℝ)*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ)))+((-1/8 : ℝ)*(((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)))+((1/3 : ℝ)*((1/4 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(1 : ℝ))+((1/4 : ℝ)*(127/256 : ℝ))))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+((1/4 : ℝ)*(1/16 : ℝ)))))) (356833209087103262669/47105282128000000000000 : ℝ) := by
    convert IntervalBounds.sub b55 b25 using 1 <;> norm_num
  have b57 : Bounds (129/1024 : ℝ) (-((1/4 : ℝ)*(((-1 : ℝ)*(127/256 : ℝ))+((-1/8 : ℝ)*(1/16 : ℝ))))) (129/1024 : ℝ) := by
    convert IntervalBounds.neg b53 using 1 <;> norm_num
  have b58 : Bounds (40447087/256000000 : ℝ) (c*(127/256 : ℝ)) (20223607/128000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b12 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b59 : Bounds (-1025233/16000000 : ℝ) (d*(1/16 : ℝ)) (-64077/1000000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b21 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b60 : Bounds (24043359/256000000 : ℝ) ((c*(127/256 : ℝ))+(d*(1/16 : ℝ))) (12021751/128000000 : ℝ) := by
    convert IntervalBounds.add b58 b59 using 1 <;> norm_num
  have b61 : Bounds (24043359/1024000000 : ℝ) ((1/4 : ℝ)*((c*(127/256 : ℝ))+(d*(1/16 : ℝ)))) (12021751/512000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b60 (by norm_num) (by norm_num) using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2818417948200324737331/47105282128000000000000 : ℝ)) b30.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3599274469631646737331/47105282128000000000000 : ℝ)) b36.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1509931077497/501232000000 : ℝ)) b38.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4492236831347/1503664000000 : ℝ)) b39.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (423362451157458521/141315846384000000 : ℝ)) b40.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (141509159737038791/47105282128000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1539937725455610889/501232000000000000 : ℝ)) b42.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (88044331085668403/30073280000000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (194226918283/93981000000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (36241725455610889/501232000000000000 : ℝ)) b25.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (21208197554497602343/2826316927680000000000 : ℝ)) b56.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (129/1024 : ℝ)) b57.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (24043359/1024000000 : ℝ)) b61.1⟩

/-- Phase 2, trial α=1, unique branch 0; reject by strict increase. -/
theorem raw_trial_4 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))) ∧
    0 < (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) ∧
    0 < (-((1 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (6235077497/501232000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.sub b9 b1 using 1 <;> norm_num
  have b11 : Bounds (16 : ℝ) (16 : ℝ) (16 : ℝ) := by
    convert IntervalBounds.exact (16 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (6019/6250 : ℝ) ((16 : ℝ)*r) (6021/6250 : ℝ) := by
    convert IntervalBounds.mul_nn b11 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b13 : Bounds (2051028421/3125000000 : ℝ) (((16 : ℝ)*r)*((1 : ℝ)-c)) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b12 b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (2051028421/3125000000 : ℝ) ((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (1047525694692797/1566350000000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))) (3143696802537593/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b10 b14 using 1 <;> norm_num
  have b16 : Bounds (1047525694692797/1566350000000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (3143696802537593/4698950000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b15 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b17 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b19 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b20 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b21 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b19 b20 using 1 <;> norm_num
  have b22 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b21 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b23 : Bounds (-3133503009/46989500000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b22 b20 using 1 <;> norm_num
  have b24 : Bounds (-16 : ℝ) (-16 : ℝ) (-16 : ℝ) := by
    convert IntervalBounds.exact (-16 : ℝ) using 1 <;> norm_num
  have b25 : Bounds (-6021/6250 : ℝ) ((-16 : ℝ)*r) (-6019/6250 : ℝ) := by
    convert IntervalBounds.mul_pn b24 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b26 : Bounds (385679463/390625000 : ℝ) (((-16 : ℝ)*r)*d) (6172927893/6250000000 : ℝ) := by
    convert IntervalBounds.mul_pp b25 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (385679463/390625000 : ℝ) ((1 : ℝ)*(((-16 : ℝ)*r)*d)) (6172927893/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b26 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b28 : Bounds (135190884109983/146842187500000 : ℝ) (((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d))) (540982197043283/587381250000000 : ℝ) := by
    convert IntervalBounds.add b23 b27 using 1 <;> norm_num
  have b29 : Bounds (0 : ℝ) ((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b17 b28 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b30 : Bounds (1047525694692797/1566350000000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d))))) (3143696802537593/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b16 b29 using 1 <;> norm_num
  have b31 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b32 : Bounds (-3143696802537593/4698950000000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (-1047525694692797/1566350000000000 : ℝ) := by
    convert IntervalBounds.mul_pn b31 b15 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b33 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b34 : Bounds (-540982197043283/4699050000000000 : ℝ) ((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))) (-135190884109983/1174737500000000 : ℝ) := by
    convert IntervalBounds.mul_pn b33 b28 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b35 : Bounds (-34628873509521622079/44161201995000000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d))))) (-115385916567588119027/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b32 b34 using 1 <;> norm_num
  have b36 : Bounds (21383133382912248829/14720400665000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) (641736504294501748523/441612019950000000000 : ℝ) := by
    convert IntervalBounds.sub b30 b35 using 1 <;> norm_num
  have b37 : Bounds (333617030771456681357/1566350000000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (500605422532888846913/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b15 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b38 : Bounds (-554632800821276159939/587381250000000000000 : ℝ) (d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))) (-8662626281115380691/9177636718750000000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b28 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b39 : Bounds (-3436211314255839235441/4699050000000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d))))) (-1717026905432648609983/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.add b37 b38 using 1 <;> norm_num
  have b40 : Bounds (103012010497255767636437441/73602003325000000000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) (618379472301735043240509739/441612019950000000000000000 : ℝ) := by
    convert IntervalBounds.sub b30 b39 using 1 <;> norm_num
  have b41 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b42 : Bounds (5746575694692797/1566350000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (17240546802537593/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b30 b41 using 1 <;> norm_num
  have b43 : Bounds (10953153197462407/4698950000000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) (3651524305307203/1566350000000000 : ℝ) := by
    convert IntervalBounds.sub b41 b30 using 1 <;> norm_num
  have b44 : Bounds (97854732475478377921/44161201995000000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (326226103382411880973/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b35 b41 using 1 <;> norm_num
  have b45 : Bounds (556997936517588119027/147204006650000000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) (167112479494521622079/44161201995000000000 : ℝ) := by
    convert IntervalBounds.sub b41 b35 using 1 <;> norm_num
  have b46 : Bounds (10660938685744160764559/4699050000000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (5331398094567351390017/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.add b39 b41 using 1 <;> norm_num
  have b47 : Bounds (8765451905432648609983/2349475000000000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))) (17533361314255839235441/4699050000000000000000 : ℝ) := by
    convert IntervalBounds.sub b41 b39 using 1 <;> norm_num
  have b48 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b49 : Bounds (633780302956717/587381250000000 : ℝ) ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))) (158493490890017/146842187500000 : ℝ) := by
    convert IntervalBounds.sub b48 b28 using 1 <;> norm_num
  have b50 : Bounds (1985753716322057/501232000000000000 : ℝ) (c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))) (2986591811472373/751832000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b51 : Bounds (133812389606597/1957937500000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))) (3212570690426097/46989500000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b23 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b52 : Bounds (36241725455610889/501232000000000000 : ℝ) ((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)))) (2175508914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b50 b51 using 1 <;> norm_num
  have b53 : Bounds (2809492513572770120321/4710528212800000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) (28108467597997600554189/47105282128000000000000 : ℝ) := by
    convert IntervalBounds.sub b30 b52 using 1 <;> norm_num
  have b54 : Bounds (653213582548501/3125000000000000 : ℝ) (c*(((16 : ℝ)*r)*((1 : ℝ)-c))) (653433643582659/3125000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b13 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b55 : Bounds (-6328689382524069/6250000000000000 : ℝ) (d*(((-16 : ℝ)*r)*d)) (-24713182950651/24414062500000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b26 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b56 : Bounds (-5022262217427067/6250000000000000 : ℝ) ((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))) (-2509853774100669/3125000000000000 : ℝ) := by
    convert IntervalBounds.add b54 b55 using 1 <;> norm_num
  have b57 : Bounds (-5022262217427067/6250000000000000 : ℝ) ((1 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d)))) (-2509853774100669/3125000000000000 : ℝ) := by
    convert IntervalBounds.mul_np b0 b56 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b58 : Bounds (2509853774100669/3125000000000000 : ℝ) (-((1 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) (5022262217427067/6250000000000000 : ℝ) := by
    convert IntervalBounds.neg b57 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (21383133382912248829/14720400665000000000 : ℝ)) b36.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (103012010497255767636437441/73602003325000000000000000 : ℝ)) b40.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (5746575694692797/1566350000000000 : ℝ)) b42.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (10953153197462407/4698950000000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (97854732475478377921/44161201995000000000 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (556997936517588119027/147204006650000000000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (10660938685744160764559/4699050000000000000000 : ℝ)) b46.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (8765451905432648609983/2349475000000000000000 : ℝ)) b47.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (633780302956717/587381250000000 : ℝ)) b49.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1047525694692797/1566350000000000 : ℝ)) b30.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2809492513572770120321/4710528212800000000000 : ℝ)) b53.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2509853774100669/3125000000000000 : ℝ)) b58.1⟩

/-- Phase 2, trial α=1/2, unique branch 0; reject by strict increase. -/
theorem raw_trial_5 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))) ∧
    0 < (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) ∧
    0 < (-((1/2 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (6235077497/501232000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.sub b9 b1 using 1 <;> norm_num
  have b11 : Bounds (1/2 : ℝ) (1/2 : ℝ) (1/2 : ℝ) := by
    convert IntervalBounds.exact (1/2 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (16 : ℝ) (16 : ℝ) (16 : ℝ) := by
    convert IntervalBounds.exact (16 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (6019/6250 : ℝ) ((16 : ℝ)*r) (6021/6250 : ℝ) := by
    convert IntervalBounds.mul_nn b12 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (2051028421/3125000000 : ℝ) (((16 : ℝ)*r)*((1 : ℝ)-c)) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b13 b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (2051028421/6250000000 : ℝ) ((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))) (4103425899/12500000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b16 : Bounds (533505155935461/1566350000000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))) (1601153352289109/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b10 b15 using 1 <;> norm_num
  have b17 : Bounds (533505155935461/1566350000000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (1601153352289109/4698950000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b18 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b20 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b21 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b22 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b20 b21 using 1 <;> norm_num
  have b23 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b22 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b24 : Bounds (-3133503009/46989500000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b23 b21 using 1 <;> norm_num
  have b25 : Bounds (-16 : ℝ) (-16 : ℝ) (-16 : ℝ) := by
    convert IntervalBounds.exact (-16 : ℝ) using 1 <;> norm_num
  have b26 : Bounds (-6021/6250 : ℝ) ((-16 : ℝ)*r) (-6019/6250 : ℝ) := by
    convert IntervalBounds.mul_pn b25 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (385679463/390625000 : ℝ) (((-16 : ℝ)*r)*d) (6172927893/6250000000 : ℝ) := by
    convert IntervalBounds.mul_pp b26 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b28 : Bounds (385679463/781250000 : ℝ) ((1/2 : ℝ)*(((-16 : ℝ)*r)*d)) (6172927893/12500000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b29 : Bounds (62699343603429/146842187500000 : ℝ) (((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d))) (501826457774533/1174762500000000 : ℝ) := by
    convert IntervalBounds.add b24 b28 using 1 <;> norm_num
  have b30 : Bounds (0 : ℝ) ((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b18 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b31 : Bounds (533505155935461/1566350000000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d))))) (1601153352289109/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b17 b30 using 1 <;> norm_num
  have b32 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b33 : Bounds (-1601153352289109/4698950000000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (-533505155935461/1566350000000000 : ℝ) := by
    convert IntervalBounds.mul_pn b32 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b34 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b35 : Bounds (-501826457774533/9398100000000000 : ℝ) ((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))) (-62699343603429/1174737500000000 : ℝ) := by
    convert IntervalBounds.mul_pn b34 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b36 : Bounds (-69623427015631668533/176644807980000000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d))))) (-57995010397917170451/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b33 b35 using 1 <;> norm_num
  have b37 : Bounds (10813329144757585977/14720400665000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) (649073121481123848523/883224039900000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b36 using 1 <;> norm_num
  have b38 : Bounds (169911255567481554741/1566350000000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (254969260971870006269/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b39 : Bounds (-514489044783557791189/1174762500000000000000 : ℝ) (d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))) (-4017585840076920033/9177636718750000000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b40 : Bounds (-1548222412431786500533/4699050000000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d))))) (-773532714087821522179/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.add b38 b39 using 1 <;> norm_num
  have b41 : Bounds (49301599859058529484801533/73602003325000000000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) (295978387299409616462590807/441612019950000000000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b40 using 1 <;> norm_num
  have b42 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b43 : Bounds (5232555155935461/1566350000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (15698003352289109/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b31 b42 using 1 <;> norm_num
  have b44 : Bounds (12495696647710891/4698950000000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) (4165544844064539/1566350000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b31 using 1 <;> norm_num
  have b45 : Bounds (460310996924368331467/176644807980000000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (383617009552082829549/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b36 b42 using 1 <;> norm_num
  have b46 : Bounds (499607030347917170451/147204006650000000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) (599557850955631668533/176644807980000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b36 using 1 <;> norm_num
  have b47 : Bounds (12548927587568213499467/4699050000000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (6274892285912178477821/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.add b40 b42 using 1 <;> norm_num
  have b48 : Bounds (7821957714087821522179/2349475000000000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))) (15645372412431786500533/4699050000000000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b40 using 1 <;> norm_num
  have b49 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b50 : Bounds (1847698542225467/1174762500000000 : ℝ) ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))) (230985031396571/146842187500000 : ℝ) := by
    convert IntervalBounds.sub b49 b29 using 1 <;> norm_num
  have b51 : Bounds (1985753716322057/501232000000000000 : ℝ) (c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))) (2986591811472373/751832000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b52 : Bounds (133812389606597/1957937500000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))) (3212570690426097/46989500000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b24 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b53 : Bounds (36241725455610889/501232000000000000 : ℝ) ((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)))) (2175508914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b51 b52 using 1 <;> norm_num
  have b54 : Bounds (1263664154792748362113/4710528212800000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/2 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/2 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) (12645024824898637908429/47105282128000000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b53 using 1 <;> norm_num
  have b55 : Bounds (653213582548501/3125000000000000 : ℝ) (c*(((16 : ℝ)*r)*((1 : ℝ)-c))) (653433643582659/3125000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b56 : Bounds (-6328689382524069/6250000000000000 : ℝ) (d*(((-16 : ℝ)*r)*d)) (-24713182950651/24414062500000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b57 : Bounds (-5022262217427067/6250000000000000 : ℝ) ((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))) (-2509853774100669/3125000000000000 : ℝ) := by
    convert IntervalBounds.add b55 b56 using 1 <;> norm_num
  have b58 : Bounds (-5022262217427067/12500000000000000 : ℝ) ((1/2 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d)))) (-2509853774100669/6250000000000000 : ℝ) := by
    convert IntervalBounds.mul_np b11 b57 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b59 : Bounds (2509853774100669/6250000000000000 : ℝ) (-((1/2 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) (5022262217427067/12500000000000000 : ℝ) := by
    convert IntervalBounds.neg b58 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (10813329144757585977/14720400665000000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (49301599859058529484801533/73602003325000000000000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (5232555155935461/1566350000000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (12495696647710891/4698950000000000 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (460310996924368331467/176644807980000000000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (499607030347917170451/147204006650000000000 : ℝ)) b46.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (12548927587568213499467/4699050000000000000000 : ℝ)) b47.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (7821957714087821522179/2349475000000000000000 : ℝ)) b48.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1847698542225467/1174762500000000 : ℝ)) b50.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (533505155935461/1566350000000000 : ℝ)) b31.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1263664154792748362113/4710528212800000000000 : ℝ)) b54.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2509853774100669/6250000000000000 : ℝ)) b59.1⟩

/-- Phase 2, trial α=1/4, unique branch 0; reject by strict increase. -/
theorem raw_trial_6 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))) ∧
    0 < (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) ∧
    0 < (-((1/4 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (6235077497/501232000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.sub b9 b1 using 1 <;> norm_num
  have b11 : Bounds (1/4 : ℝ) (1/4 : ℝ) (1/4 : ℝ) := by
    convert IntervalBounds.exact (1/4 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (16 : ℝ) (16 : ℝ) (16 : ℝ) := by
    convert IntervalBounds.exact (16 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (6019/6250 : ℝ) ((16 : ℝ)*r) (6021/6250 : ℝ) := by
    convert IntervalBounds.mul_nn b12 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (2051028421/3125000000 : ℝ) (((16 : ℝ)*r)*((1 : ℝ)-c)) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b13 b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (2051028421/12500000000 : ℝ) ((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))) (4103425899/25000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b16 : Bounds (276494886556793/1566350000000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))) (829881627164867/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b10 b15 using 1 <;> norm_num
  have b17 : Bounds (276494886556793/1566350000000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (829881627164867/4698950000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b18 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b20 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b21 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b22 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b20 b21 using 1 <;> norm_num
  have b23 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b22 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b24 : Bounds (-3133503009/46989500000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b23 b21 using 1 <;> norm_num
  have b25 : Bounds (-16 : ℝ) (-16 : ℝ) (-16 : ℝ) := by
    convert IntervalBounds.exact (-16 : ℝ) using 1 <;> norm_num
  have b26 : Bounds (-6021/6250 : ℝ) ((-16 : ℝ)*r) (-6019/6250 : ℝ) := by
    convert IntervalBounds.mul_pn b25 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (385679463/390625000 : ℝ) (((-16 : ℝ)*r)*d) (6172927893/6250000000 : ℝ) := by
    convert IntervalBounds.mul_pp b26 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b28 : Bounds (385679463/1562500000 : ℝ) ((1/4 : ℝ)*(((-16 : ℝ)*r)*d)) (6172927893/25000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b29 : Bounds (3306696668769/18355273437500 : ℝ) (((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d))) (423514979237033/2349525000000000 : ℝ) := by
    convert IntervalBounds.add b24 b28 using 1 <;> norm_num
  have b30 : Bounds (0 : ℝ) ((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b18 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b31 : Bounds (276494886556793/1566350000000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d))))) (829881627164867/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b17 b30 using 1 <;> norm_num
  have b32 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b33 : Bounds (-829881627164867/4698950000000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (-276494886556793/1566350000000000 : ℝ) := by
    convert IntervalBounds.mul_pn b32 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b34 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b35 : Bounds (-423514979237033/18796200000000000 : ℝ) ((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))) (-3306696668769/146842187500000 : ℝ) := by
    convert IntervalBounds.mul_pn b34 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b36 : Bounds (-70354787008808517283/353289615960000000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d))))) (-29299557313081696163/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b33 b35 using 1 <;> norm_num
  have b37 : Bounds (5528427025680254551/14720400665000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) (663746355854368048523/1766448079800000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b36 using 1 <;> norm_num
  have b38 : Bounds (88058367965493991433/1566350000000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (132151180191360585947/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b39 : Bounds (-434201532708121053689/2349525000000000000000 : ℝ) (d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))) (-211883202444711213/1147204589843750000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b40 : Bounds (-604227961519760133079/4699050000000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d))))) (-301785618415407978277/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.add b38 b39 using 1 <;> norm_num
  have b41 : Bounds (22446394539959910408983579/73602003325000000000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) (134777844798246903073631341/441612019950000000000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b40 using 1 <;> norm_num
  have b42 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b43 : Bounds (4975544886556793/1566350000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (14926731627164867/4698950000000000 : ℝ) := by
    convert IntervalBounds.add b31 b42 using 1 <;> norm_num
  have b44 : Bounds (13266968372835133/4698950000000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) (4422555113443207/1566350000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b31 using 1 <;> norm_num
  have b45 : Bounds (989514060871191482717/353289615960000000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (412312462636918303837/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b36 b42 using 1 <;> norm_num
  have b46 : Bounds (470911577263081696163/147204006650000000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) (1130223634888808517283/353289615960000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b36 using 1 <;> norm_num
  have b47 : Bounds (13492922038480239866921/4699050000000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (6746639381584592021723/2349475000000000000000 : ℝ) := by
    convert IntervalBounds.add b40 b42 using 1 <;> norm_num
  have b48 : Bounds (7350210618415407978277/2349475000000000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))) (14701377961519760133079/4699050000000000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b40 using 1 <;> norm_num
  have b49 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b50 : Bounds (4275535020762967/2349525000000000 : ℝ) ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))) (33403850206231/18355273437500 : ℝ) := by
    convert IntervalBounds.sub b49 b29 using 1 <;> norm_num
  have b51 : Bounds (1985753716322057/501232000000000000 : ℝ) (c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))) (2986591811472373/751832000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b52 : Bounds (133812389606597/1957937500000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))) (3212570690426097/46989500000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b24 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b53 : Bounds (36241725455610889/501232000000000000 : ℝ) ((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)))) (2175508914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b51 b52 using 1 <;> norm_num
  have b54 : Bounds (490749975402737483009/4710528212800000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/4 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/4 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) (4913303438349156585549/47105282128000000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b53 using 1 <;> norm_num
  have b55 : Bounds (653213582548501/3125000000000000 : ℝ) (c*(((16 : ℝ)*r)*((1 : ℝ)-c))) (653433643582659/3125000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b56 : Bounds (-6328689382524069/6250000000000000 : ℝ) (d*(((-16 : ℝ)*r)*d)) (-24713182950651/24414062500000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b57 : Bounds (-5022262217427067/6250000000000000 : ℝ) ((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))) (-2509853774100669/3125000000000000 : ℝ) := by
    convert IntervalBounds.add b55 b56 using 1 <;> norm_num
  have b58 : Bounds (-5022262217427067/25000000000000000 : ℝ) ((1/4 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d)))) (-2509853774100669/12500000000000000 : ℝ) := by
    convert IntervalBounds.mul_np b11 b57 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b59 : Bounds (2509853774100669/12500000000000000 : ℝ) (-((1/4 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) (5022262217427067/25000000000000000 : ℝ) := by
    convert IntervalBounds.neg b58 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (5528427025680254551/14720400665000000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (22446394539959910408983579/73602003325000000000000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4975544886556793/1566350000000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (13266968372835133/4698950000000000 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (989514060871191482717/353289615960000000000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (470911577263081696163/147204006650000000000 : ℝ)) b46.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (13492922038480239866921/4699050000000000000000 : ℝ)) b47.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (7350210618415407978277/2349475000000000000000 : ℝ)) b48.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4275535020762967/2349525000000000 : ℝ)) b50.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (276494886556793/1566350000000000 : ℝ)) b31.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (490749975402737483009/4710528212800000000000 : ℝ)) b54.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2509853774100669/12500000000000000 : ℝ)) b59.1⟩

/-- Phase 2, trial α=1/8, unique branch 0; reject by strict increase. -/
theorem raw_trial_7 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))) ∧
    0 < (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) ∧
    0 < (-((1/8 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (6235077497/501232000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.sub b9 b1 using 1 <;> norm_num
  have b11 : Bounds (1/8 : ℝ) (1/8 : ℝ) (1/8 : ℝ) := by
    convert IntervalBounds.exact (1/8 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (16 : ℝ) (16 : ℝ) (16 : ℝ) := by
    convert IntervalBounds.exact (16 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (6019/6250 : ℝ) ((16 : ℝ)*r) (6021/6250 : ℝ) := by
    convert IntervalBounds.mul_nn b12 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (2051028421/3125000000 : ℝ) (((16 : ℝ)*r)*((1 : ℝ)-c)) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b13 b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (2051028421/25000000000 : ℝ) ((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))) (4103425899/50000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b16 : Bounds (147989751867459/1566350000000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))) (222122882301373/2349475000000000 : ℝ) := by
    convert IntervalBounds.add b10 b15 using 1 <;> norm_num
  have b17 : Bounds (147989751867459/1566350000000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (222122882301373/2349475000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b18 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b20 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b21 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b22 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b20 b21 using 1 <;> norm_num
  have b23 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b22 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b24 : Bounds (-3133503009/46989500000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b23 b21 using 1 <;> norm_num
  have b25 : Bounds (-16 : ℝ) (-16 : ℝ) (-16 : ℝ) := by
    convert IntervalBounds.exact (-16 : ℝ) using 1 <;> norm_num
  have b26 : Bounds (-6021/6250 : ℝ) ((-16 : ℝ)*r) (-6019/6250 : ℝ) := by
    convert IntervalBounds.mul_pn b25 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (385679463/390625000 : ℝ) (((-16 : ℝ)*r)*d) (6172927893/6250000000 : ℝ) := by
    convert IntervalBounds.mul_pp b26 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b28 : Bounds (385679463/3125000000 : ℝ) ((1/8 : ℝ)*(((-16 : ℝ)*r)*d)) (6172927893/50000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b29 : Bounds (16661376447027/293684375000000 : ℝ) (((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d))) (266892022162033/4699050000000000 : ℝ) := by
    convert IntervalBounds.add b24 b28 using 1 <;> norm_num
  have b30 : Bounds (0 : ℝ) ((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b18 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b31 : Bounds (147989751867459/1566350000000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d))))) (222122882301373/2349475000000000 : ℝ) := by
    convert IntervalBounds.add b17 b30 using 1 <;> norm_num
  have b32 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b33 : Bounds (-222122882301373/2349475000000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (-147989751867459/1566350000000000 : ℝ) := by
    convert IntervalBounds.mul_pn b32 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b34 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b35 : Bounds (-266892022162033/37592400000000000 : ℝ) ((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))) (-16661376447027/2349475000000000 : ℝ) := by
    convert IntervalBounds.mul_pn b34 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b36 : Bounds (-71817506995162214783/706579231920000000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d))))) (-14951830770663959019/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b33 b35 using 1 <;> norm_num
  have b37 : Bounds (1442987983070794419/7360200332500000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) (693092824600856448523/3532896159600000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b36 using 1 <;> norm_num
  have b38 : Bounds (47131924164500209779/1566350000000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (35371069900552937893/1174737500000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b39 : Bounds (-273626508557247578689/4699050000000000000000 : ℝ) (d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))) (-1067611018596149079/18355273437500000000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b40 : Bounds (-16528842007968368669/587381250000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d))))) (-32956035289600603163/1174737500000000000000 : ℝ) := by
    convert IntervalBounds.add b38 b39 using 1 <;> norm_num
  have b41 : Bounds (4509395940205300435537301/36801001662500000000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) (6772196693458193297393951/55201502493750000000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b40 using 1 <;> norm_num
  have b42 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b43 : Bounds (4847039751867459/1566350000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (7270547882301373/2349475000000000 : ℝ) := by
    convert IntervalBounds.add b31 b42 using 1 <;> norm_num
  have b44 : Bounds (6826302117698627/2349475000000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) (4551060248132541/1566350000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b31 using 1 <;> norm_num
  have b45 : Bounds (2047920188764837785217/706579231920000000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (426660189179336040981/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b36 b42 using 1 <;> norm_num
  have b46 : Bounds (456563850720663959019/147204006650000000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) (2191555202755162214783/706579231920000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b36 using 1 <;> norm_num
  have b47 : Bounds (1745614907992031631331/587381250000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (3491256464710399396837/1174737500000000000000 : ℝ) := by
    convert IntervalBounds.add b40 b42 using 1 <;> norm_num
  have b48 : Bounds (3557168535289600603163/1174737500000000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))) (1778672592007968368669/587381250000000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b40 using 1 <;> norm_num
  have b49 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b50 : Bounds (9131207977837967/4699050000000000 : ℝ) ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))) (570707373552973/293684375000000 : ℝ) := by
    convert IntervalBounds.sub b49 b29 using 1 <;> norm_num
  have b51 : Bounds (1985753716322057/501232000000000000 : ℝ) (c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))) (2986591811472373/751832000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b52 : Bounds (133812389606597/1957937500000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))) (3212570690426097/46989500000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b24 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b53 : Bounds (36241725455610889/501232000000000000 : ℝ) ((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)))) (2175508914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b51 b52 using 1 <;> norm_num
  have b54 : Bounds (104292885707732043457/4710528212800000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/8 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/8 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))) (1047442745074415924109/47105282128000000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b53 using 1 <;> norm_num
  have b55 : Bounds (653213582548501/3125000000000000 : ℝ) (c*(((16 : ℝ)*r)*((1 : ℝ)-c))) (653433643582659/3125000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b56 : Bounds (-6328689382524069/6250000000000000 : ℝ) (d*(((-16 : ℝ)*r)*d)) (-24713182950651/24414062500000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b57 : Bounds (-5022262217427067/6250000000000000 : ℝ) ((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))) (-2509853774100669/3125000000000000 : ℝ) := by
    convert IntervalBounds.add b55 b56 using 1 <;> norm_num
  have b58 : Bounds (-5022262217427067/50000000000000000 : ℝ) ((1/8 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d)))) (-2509853774100669/25000000000000000 : ℝ) := by
    convert IntervalBounds.mul_np b11 b57 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b59 : Bounds (2509853774100669/25000000000000000 : ℝ) (-((1/8 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) (5022262217427067/50000000000000000 : ℝ) := by
    convert IntervalBounds.neg b58 using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1442987983070794419/7360200332500000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4509395940205300435537301/36801001662500000000000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4847039751867459/1566350000000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (6826302117698627/2349475000000000 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2047920188764837785217/706579231920000000000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (456563850720663959019/147204006650000000000 : ℝ)) b46.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1745614907992031631331/587381250000000000000 : ℝ)) b47.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3557168535289600603163/1174737500000000000000 : ℝ)) b48.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (9131207977837967/4699050000000000 : ℝ)) b50.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (147989751867459/1566350000000000 : ℝ)) b31.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (104292885707732043457/4710528212800000000000 : ℝ)) b54.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2509853774100669/25000000000000000 : ℝ)) b59.1⟩

/-- Phase 2, trial α=1/16, unique branch 0; accept. -/
theorem raw_trial_8 {c d r : ℝ}
    (hc : Bounds (318481/1000000) c (318482/1000000))
    (hd : Bounds (-1025233/1000000) d (-1025232/1000000))
    (hr : Bounds (6019/100000) r (6021/100000)) :
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) ∧
    0 < ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))) ∧
    0 < (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d))))) ∧
    0 < ((((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))+((1/3 : ℝ)*((1/16 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) ∧
    0 < (-((1/16 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) ∧
    0 < ((1/16 : ℝ)*(((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))) := by
  have b0 : Bounds (1 : ℝ) (1 : ℝ) (1 : ℝ) := by
    convert IntervalBounds.exact (1 : ℝ) using 1 <;> norm_num
  have b1 : Bounds (897/1024 : ℝ) (897/1024 : ℝ) (897/1024 : ℝ) := by
    convert IntervalBounds.exact (897/1024 : ℝ) using 1 <;> norm_num
  have b4 : Bounds (340759/500000 : ℝ) ((1 : ℝ)-c) (681519/1000000 : ℝ) := by
    convert IntervalBounds.sub b0 hc using 1 <;> norm_num
  have b5 : Bounds (2051028421/50000000000 : ℝ) (r*((1 : ℝ)-c)) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hr b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b6 : Bounds (83494230351/100000000000 : ℝ) ((897/1024 : ℝ)-(r*((1 : ℝ)-c))) (5218474963/6250000000 : ℝ) := by
    convert IntervalBounds.sub b1 b5 using 1 <;> norm_num
  have b7 : Bounds (93979/100000 : ℝ) ((1 : ℝ)-r) (93981/100000 : ℝ) := by
    convert IntervalBounds.sub b0 hr using 1 <;> norm_num
  have b8 : Bounds (100000/93981 : ℝ) (((1 : ℝ)-r))⁻¹ (100000/93979 : ℝ) := by
    convert IntervalBounds.inv_pos b7 (by norm_num) using 1 <;> norm_num
  have b9 : Bounds (27831410117/31327000000 : ℝ) (((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹) (5218474963/5873687500 : ℝ) := by
    convert IntervalBounds.mul_nn b6 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b10 : Bounds (6235077497/501232000000 : ℝ) ((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)) (18755168653/1503664000000 : ℝ) := by
    convert IntervalBounds.sub b9 b1 using 1 <;> norm_num
  have b11 : Bounds (1/16 : ℝ) (1/16 : ℝ) (1/16 : ℝ) := by
    convert IntervalBounds.exact (1/16 : ℝ) using 1 <;> norm_num
  have b12 : Bounds (16 : ℝ) (16 : ℝ) (16 : ℝ) := by
    convert IntervalBounds.exact (16 : ℝ) using 1 <;> norm_num
  have b13 : Bounds (6019/6250 : ℝ) ((16 : ℝ)*r) (6021/6250 : ℝ) := by
    convert IntervalBounds.mul_nn b12 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b14 : Bounds (2051028421/3125000000 : ℝ) (((16 : ℝ)*r)*((1 : ℝ)-c)) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b13 b4 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b15 : Bounds (2051028421/50000000000 : ℝ) ((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b16 : Bounds (10467148065349/195793750000000 : ℝ) (((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))) (502855666643371/9397900000000000 : ℝ) := by
    convert IntervalBounds.add b10 b15 using 1 <;> norm_num
  have b17 : Bounds (10467148065349/195793750000000 : ℝ) ((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (502855666643371/9397900000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b18 : Bounds (0 : ℝ) (0 : ℝ) (0 : ℝ) := by
    convert IntervalBounds.exact (0 : ℝ) using 1 <;> norm_num
  have b20 : Bounds (-6172927893/100000000000 : ℝ) (r*d) (-385679463/6250000000 : ℝ) := by
    convert IntervalBounds.mul_np hr hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b21 : Bounds (1/64 : ℝ) (1/64 : ℝ) (1/64 : ℝ) := by
    convert IntervalBounds.exact (1/64 : ℝ) using 1 <;> norm_num
  have b22 : Bounds (-7735427893/100000000000 : ℝ) ((r*d)-(1/64 : ℝ)) (-483335713/6250000000 : ℝ) := by
    convert IntervalBounds.sub b20 b21 using 1 <;> norm_num
  have b23 : Bounds (-7735427893/93979000000 : ℝ) (((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹) (-483335713/5873812500 : ℝ) := by
    convert IntervalBounds.mul_pn b22 b8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b24 : Bounds (-3133503009/46989500000 : ℝ) ((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)) (-6264918283/93981000000 : ℝ) := by
    convert IntervalBounds.add b23 b21 using 1 <;> norm_num
  have b25 : Bounds (-16 : ℝ) (-16 : ℝ) (-16 : ℝ) := by
    convert IntervalBounds.exact (-16 : ℝ) using 1 <;> norm_num
  have b26 : Bounds (-6021/6250 : ℝ) ((-16 : ℝ)*r) (-6019/6250 : ℝ) := by
    convert IntervalBounds.mul_pn b25 hr (by norm_num) (by norm_num) using 1 <;> norm_num
  have b27 : Bounds (385679463/390625000 : ℝ) (((-16 : ℝ)*r)*d) (6172927893/6250000000 : ℝ) := by
    convert IntervalBounds.mul_pp b26 hd (by norm_num) (by norm_num) using 1 <;> norm_num
  have b28 : Bounds (385679463/6250000000 : ℝ) ((1/16 : ℝ)*(((-16 : ℝ)*r)*d)) (6172927893/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b29 : Bounds (-2923017359223/587368750000000 : ℝ) (((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d))) (-46353891987967/9398100000000000 : ℝ) := by
    convert IntervalBounds.add b24 b28 using 1 <;> norm_num
  have b30 : Bounds (0 : ℝ) ((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))) (0 : ℝ) := by
    convert IntervalBounds.mul_np b18 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b31 : Bounds (10467148065349/195793750000000 : ℝ) (((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d))))) (502855666643371/9397900000000000 : ℝ) := by
    convert IntervalBounds.add b17 b30 using 1 <;> norm_num
  have b32 : Bounds (-1 : ℝ) (-1 : ℝ) (-1 : ℝ) := by
    convert IntervalBounds.exact (-1 : ℝ) using 1 <;> norm_num
  have b33 : Bounds (-502855666643371/9397900000000000 : ℝ) ((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (-10467148065349/195793750000000 : ℝ) := by
    convert IntervalBounds.mul_pn b32 b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b34 : Bounds (-1/8 : ℝ) (-1/8 : ℝ) (-1/8 : ℝ) := by
    convert IntervalBounds.exact (-1/8 : ℝ) using 1 <;> norm_num
  have b35 : Bounds (46353891987967/75184800000000000 : ℝ) ((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))) (2923017359223/4698950000000000 : ℝ) := by
    convert IntervalBounds.mul_pp b34 b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b36 : Bounds (-74742946967869609783/1413158463840000000000 : ℝ) (((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d))))) (-7777967499455090447/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b33 b35 using 1 <;> norm_num
  have b37 : Bounds (3129500872744511963/29440801330000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) (751785762093833248523/7065792319200000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b36 using 1 <;> norm_num
  have b38 : Bounds (3333587783000414869/195793750000000000000 : ℝ) (c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))))) (80075239211957041411/4698950000000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b16 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b39 : Bounds (990072778970987153/195793750000000000000 : ℝ) (d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))) (2996773856248273959/587368750000000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b29 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b40 : Bounds (2161830280985701011/97896875000000000000 : ℝ) ((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d))))) (104049430061943233083/4698950000000000000000 : ℝ) := by
    convert IntervalBounds.add b38 b39 using 1 <;> norm_num
  have b41 : Bounds (4609980368716973705208859/147204006650000000000000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) (289113335427522408343481/9200250415625000000000000 : ℝ) := by
    convert IntervalBounds.sub b31 b40 using 1 <;> norm_num
  have b42 : Bounds (3 : ℝ) (3 : ℝ) (3 : ℝ) := by
    convert IntervalBounds.exact (3 : ℝ) using 1 <;> norm_num
  have b43 : Bounds (597848398065349/195793750000000 : ℝ) ((((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (28696555666643371/9397900000000000 : ℝ) := by
    convert IntervalBounds.add b31 b42 using 1 <;> norm_num
  have b44 : Bounds (27690844333356629/9397900000000000 : ℝ) ((3 : ℝ)-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) (576914101934651/195793750000000 : ℝ) := by
    convert IntervalBounds.sub b42 b31 using 1 <;> norm_num
  have b45 : Bounds (4164732444552130390217/1413158463840000000000 : ℝ) ((((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (433834052450544909553/147204006650000000000 : ℝ) := by
    convert IntervalBounds.add b36 b42 using 1 <;> norm_num
  have b46 : Bounds (449389987449455090447/147204006650000000000 : ℝ) ((3 : ℝ)-(((-1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((-1/8 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) (4314218338487869609783/1413158463840000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b36 using 1 <;> norm_num
  have b47 : Bounds (295852455280985701011/97896875000000000000 : ℝ) (((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))+(3 : ℝ)) (14200899430061943233083/4698950000000000000000 : ℝ) := by
    convert IntervalBounds.add b40 b42 using 1 <;> norm_num
  have b48 : Bounds (13992800569938056766917/4698950000000000000000 : ℝ) ((3 : ℝ)-((c*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+(d*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) (291528794719014298989/97896875000000000000 : ℝ) := by
    convert IntervalBounds.sub b42 b40 using 1 <;> norm_num
  have b49 : Bounds (2 : ℝ) (2 : ℝ) (2 : ℝ) := by
    convert IntervalBounds.exact (2 : ℝ) using 1 <;> norm_num
  have b50 : Bounds (18842553891987967/9398100000000000 : ℝ) ((2 : ℝ)-(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))) (1177660517359223/587368750000000 : ℝ) := by
    convert IntervalBounds.sub b49 b29 using 1 <;> norm_num
  have b51 : Bounds (1985753716322057/501232000000000000 : ℝ) (c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))) (2986591811472373/751832000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b10 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b52 : Bounds (133812389606597/1957937500000000 : ℝ) (d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))) (3212570690426097/46989500000000000 : ℝ) := by
    convert IntervalBounds.mul_pp hd b24 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b53 : Bounds (36241725455610889/501232000000000000 : ℝ) ((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ)))) (2175508914331597/30073280000000000 : ℝ) := by
    convert IntervalBounds.add b51 b52 using 1 <;> norm_num
  have b54 : Bounds (1/3 : ℝ) (1/3 : ℝ) (1/3 : ℝ) := by
    convert IntervalBounds.exact (1/3 : ℝ) using 1 <;> norm_num
  have b55 : Bounds (653213582548501/3125000000000000 : ℝ) (c*(((16 : ℝ)*r)*((1 : ℝ)-c))) (653433643582659/3125000000000000 : ℝ) := by
    convert IntervalBounds.mul_nn hc b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b56 : Bounds (-6328689382524069/6250000000000000 : ℝ) (d*(((-16 : ℝ)*r)*d)) (-24713182950651/24414062500000 : ℝ) := by
    convert IntervalBounds.mul_pn hd b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b57 : Bounds (-5022262217427067/6250000000000000 : ℝ) ((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))) (-2509853774100669/3125000000000000 : ℝ) := by
    convert IntervalBounds.add b55 b56 using 1 <;> norm_num
  have b58 : Bounds (-5022262217427067/100000000000000000 : ℝ) ((1/16 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d)))) (-2509853774100669/50000000000000000 : ℝ) := by
    convert IntervalBounds.mul_np b11 b57 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b59 : Bounds (-5022262217427067/300000000000000000 : ℝ) ((1/3 : ℝ)*((1/16 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) (-836617924700223/50000000000000000 : ℝ) := by
    convert IntervalBounds.mul_np b54 b58 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b60 : Bounds (522199943807366440841/9398100000000000000000 : ℝ) (((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))+((1/3 : ℝ)*((1/16 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d)))))) (261298751918909773933/4698950000000000000000 : ℝ) := by
    convert IntervalBounds.add b53 b59 using 1 <;> norm_num
  have b61 : Bounds (1816950112261840792796339/883224039900000000000000000 : ℝ) ((((c*((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ)))+(d*((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))))+((1/3 : ℝ)*((1/16 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))))-(((1 : ℝ)*(((((897/1024 : ℝ)-(r*((1 : ℝ)-c)))*(((1 : ℝ)-r))⁻¹)-(897/1024 : ℝ))+((1/16 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))))+((0 : ℝ)*(((((r*d)-(1/64 : ℝ))*(((1 : ℝ)-r))⁻¹)+(1/64 : ℝ))+((1/16 : ℝ)*(((-16 : ℝ)*r)*d)))))) (316169137096217119999091/147204006650000000000000000 : ℝ) := by
    convert IntervalBounds.sub b60 b31 using 1 <;> norm_num
  have b62 : Bounds (2509853774100669/50000000000000000 : ℝ) (-((1/16 : ℝ)*((c*(((16 : ℝ)*r)*((1 : ℝ)-c)))+(d*(((-16 : ℝ)*r)*d))))) (5022262217427067/100000000000000000 : ℝ) := by
    convert IntervalBounds.neg b58 using 1 <;> norm_num
  have b63 : Bounds (2051028421/3125000000 : ℝ) ((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c))) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.mul_nn b0 b14 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b64 : Bounds (0 : ℝ) ((0 : ℝ)*(((-16 : ℝ)*r)*d)) (0 : ℝ) := by
    convert IntervalBounds.mul_nn b18 b27 (by norm_num) (by norm_num) using 1 <;> norm_num
  have b65 : Bounds (2051028421/3125000000 : ℝ) (((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))+((0 : ℝ)*(((-16 : ℝ)*r)*d))) (4103425899/6250000000 : ℝ) := by
    convert IntervalBounds.add b63 b64 using 1 <;> norm_num
  have b66 : Bounds (2051028421/50000000000 : ℝ) ((1/16 : ℝ)*(((1 : ℝ)*(((16 : ℝ)*r)*((1 : ℝ)-c)))+((0 : ℝ)*(((-16 : ℝ)*r)*d)))) (4103425899/100000000000 : ℝ) := by
    convert IntervalBounds.mul_nn b11 b65 (by norm_num) (by norm_num) using 1 <;> norm_num
  exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3129500872744511963/29440801330000000000 : ℝ)) b37.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4609980368716973705208859/147204006650000000000000000 : ℝ)) b41.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (597848398065349/195793750000000 : ℝ)) b43.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (27690844333356629/9397900000000000 : ℝ)) b44.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4164732444552130390217/1413158463840000000000 : ℝ)) b45.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (449389987449455090447/147204006650000000000 : ℝ)) b46.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (295852455280985701011/97896875000000000000 : ℝ)) b47.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (13992800569938056766917/4698950000000000000000 : ℝ)) b48.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (18842553891987967/9398100000000000 : ℝ)) b50.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (10467148065349/195793750000000 : ℝ)) b31.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1816950112261840792796339/883224039900000000000000000 : ℝ)) b61.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2509853774100669/50000000000000000 : ℝ)) b62.1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2051028421/50000000000 : ℝ)) b66.1⟩

end BfgsVerification.SeedOrbit
