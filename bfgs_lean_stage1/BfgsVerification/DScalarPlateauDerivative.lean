import BfgsVerification.DScalarAssembly

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.DScalar
open DScalarGeometric

theorem phi_hasDerivAt_plateau {b h : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| < scale m/2) :
    HasDerivAt (phi b) ((scale m)^2) (b*scale m+h) := by
  have hc : Continuous (fun y : ℝ => |y-b*scale m|) := (continuous_id.sub continuous_const).abs
  have hx : |b*scale m+h-b*scale m| < scale m/2 := by simpa only [add_sub_cancel_left] using hh
  have heq : phi b =ᶠ[𝓝 (b*scale m+h)] (fun y => (scale m)^3+(scale m)^2*(y-b*scale m)) := by
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hx] with y hy
    have he : b*scale m+(y-b*scale m)=y := by abel
    simpa only [he] using phi_plateau hl hr m (le_of_lt hy)
  have hd : HasDerivAt (fun y : ℝ => (scale m)^3+(scale m)^2*(y-b*scale m))
      ((scale m)^2) (b*scale m+h) := by
    simpa using (((hasDerivAt_id (b*scale m+h)).sub_const (b*scale m)).const_mul ((scale m)^2)).const_add ((scale m)^3)
  exact hd.congr_of_eventuallyEq heq

theorem phiFirst_plateau {b h : ℝ} (hl : 2 ≤ b) (hr : b ≤ 34) (m : ℕ)
    (hh : |h| < scale m/2) : phiFirst b (b*scale m+h)=(scale m)^2 :=
  (phi_hasDerivAt hl hr _).unique (phi_hasDerivAt_plateau hl hr m hh)

end BfgsVerification.DScalar
