import BfgsVerification.LScalarStepEnvelope

noncomputable section
open scoped Topology BigOperators
open Set Filter
namespace BfgsVerification.LScalarStep
open LScalarGeometric

def AffineGerm (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ a c : ℝ, f =ᶠ[𝓝 x] (fun y => a*y+c)

def BinaryAffineGerm (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ a c A C : ℝ, f =ᶠ[𝓝 x] (fun y => max (a*y+c) (A*y+C))

theorem AffineGerm.binary {f : ℝ → ℝ} {x : ℝ} (h : AffineGerm f x) : BinaryAffineGerm f x := by
  obtain ⟨a,c,he⟩ := h
  exact ⟨a,c,a,c,by simpa only [max_self] using he⟩

theorem phi_affine_at_node {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (n : ℕ) :
    AffineGerm (phi b) (b*scale n) := by
  refine ⟨scale n,(1-b)*(scale n)^2,?_⟩
  have hopen : IsOpen {y : ℝ | |y-b*scale n| < scale n/2} :=
    isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const
  have hmem : b*scale n ∈ {y : ℝ | |y-b*scale n| < scale n/2} := by
    simp only [mem_setOf_eq, sub_self, abs_zero]
    have := scale_pos n
    positivity
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have he := phi_plateau hl hr n (h := y-b*scale n) (show |y-b*scale n| ≤ scale n/2 from hy.le)
  rw [add_sub_cancel] at he
  rw [he]
  ring

theorem phi_binary_affine_of_ne_zero {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) (hx : x ≠ 0) :
    BinaryAffineGerm (phi b) x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · apply AffineGerm.binary
    refine ⟨-1,0,?_⟩
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [phi_eq_negative hl hr (show y ≤ 0 from hy.le)]
    ring
  · by_cases hxb : b < x
    · apply AffineGerm.binary
      refine ⟨1,1-b,?_⟩
      filter_upwards [Ioi_mem_nhds hxb] with y hy
      rw [phi_eq_outer hl hr (show b ≤ y from hy.le)]
      ring
    · obtain ⟨n,hlo,hhi⟩ := positive_interval_cover (by linarith : 0 < b) hx (le_of_not_gt hxb)
      by_cases he : x = b*scale n
      · rw [he]
        exact (phi_affine_at_node hl hr n).binary
      · have hstrict : x < b*scale n := lt_of_le_of_ne hhi he
        refine ⟨scale (n+1),(1-b)*(scale (n+1))^2,scale n,(1-b)*(scale n)^2,?_⟩
        filter_upwards [Ioo_mem_nhds hlo hstrict] with y hy
        have hy0 : 0 ≤ y := (mul_pos (mul_pos (by linarith : 0 < b) theta_pos) (scale_pos n)).le.trans hy.1.le
        rw [phi_eq_positive hy0, positivePart_interval_max hl hr n hy.1.le hy.2.le]
        rfl

theorem affine_of_differentiable_binary {f : ℝ → ℝ} {x : ℝ}
    (h : BinaryAffineGerm f x) (hd : DifferentiableAt ℝ f x) : AffineGerm f x := by
  obtain ⟨a,c,A,C,he⟩ := h
  rcases lt_trichotomy (a*x+c) (A*x+C) with hlt | heq | hgt
  · refine ⟨A,C,?_⟩
    have hopen : IsOpen {y : ℝ | a*y+c < A*y+C} := isOpen_lt (by fun_prop) (by fun_prop)
    filter_upwards [he,hopen.mem_nhds hlt] with y hy hlt'
    exact hy.trans (max_eq_right hlt'.le)
  · have hval : f x = a*x+c := by
      calc f x = max (a*x+c) (A*x+C) := he.self_of_nhds
           _ = a*x+c := by rw [← heq, max_self]
    have hmin : IsLocalMin (fun y => f y-(a*y+c)) x := by
      filter_upwards [he] with y hy
      rw [hval,sub_self,hy]
      exact sub_nonneg.mpr (le_max_left _ _)
    have hmin' : IsLocalMin (fun y => f y-(A*y+C)) x := by
      filter_upwards [he] with y hy
      rw [hval,heq,sub_self,hy]
      exact sub_nonneg.mpr (le_max_right _ _)
    have ha : HasDerivAt (fun y : ℝ => a*y+c) a x := by
      convert ((hasDerivAt_id x).const_mul a).add_const c using 1 <;> ring
    have hA : HasDerivAt (fun y : ℝ => A*y+C) A x := by
      convert ((hasDerivAt_id x).const_mul A).add_const C using 1 <;> ring
    have hda := hmin.hasDerivAt_eq_zero (hd.hasDerivAt.sub ha)
    have hdA := hmin'.hasDerivAt_eq_zero (hd.hasDerivAt.sub hA)
    have haA : a = A := by linarith
    have hcC : c = C := by rw [haA] at heq; linarith
    exact ⟨a,c,by simpa only [← haA, ← hcC, max_self] using he⟩
  · refine ⟨a,c,?_⟩
    have hopen : IsOpen {y : ℝ | A*y+C < a*y+c} := isOpen_lt (by fun_prop) (by fun_prop)
    filter_upwards [he,hopen.mem_nhds hgt] with y hy hgt'
    exact hy.trans (max_eq_left hgt'.le)

theorem phi_not_differentiable_zero {b : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34) :
    ¬DifferentiableAt ℝ (phi b) 0 := by
  intro hd
  have hmin : IsLocalMin (phi b) 0 := by
    apply Eventually.of_forall
    intro y
    rw [phi_zero hl hr]
    exact phi_nonnegative b y
  have hmin' : IsLocalMin (fun y => phi b y+y) 0 := by
    apply Eventually.of_forall
    intro y
    change phi b 0+0 ≤ phi b y+y
    rw [phi_zero hl hr,zero_add]
    have h0 := positivePart_nonnegative b y
    have hm := le_max_right (0 : ℝ) (-y)
    dsimp [phi]
    linarith
  have h0 := hmin.hasDerivAt_eq_zero hd.hasDerivAt
  have h1 := hmin'.hasDerivAt_eq_zero (hd.hasDerivAt.add (hasDerivAt_id 0))
  linarith

theorem phi_affine_at_differentiable {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hd : DifferentiableAt ℝ (phi b) x) : AffineGerm (phi b) x := by
  have hx : x ≠ 0 := by intro he; subst x; exact phi_not_differentiable_zero hl hr hd
  exact affine_of_differentiable_binary (phi_binary_affine_of_ne_zero hl hr hx) hd

theorem phi_second_zero_at_differentiable {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hd : DifferentiableAt ℝ (phi b) x) : HasDerivAt (deriv (phi b)) 0 x := by
  obtain ⟨a,c,he⟩ := phi_affine_at_differentiable hl hr hd
  have hder : deriv (phi b) =ᶠ[𝓝 x] (fun _ => a) := by
    filter_upwards [he.deriv] with y hy
    rw [hy]
    convert (((hasDerivAt_id y).const_mul a).add_const c).deriv using 1 <;> ring
  exact (hasDerivAt_const x a).congr_of_eventuallyEq hder

theorem phi_contDiffAt_differentiable {b x : ℝ} (hl : 17/10 ≤ b) (hr : b ≤ 34)
    (hd : DifferentiableAt ℝ (phi b) x) (N : WithTop ℕ∞) : ContDiffAt ℝ N (phi b) x := by
  obtain ⟨a,c,he⟩ := phi_affine_at_differentiable hl hr hd
  have hc : ContDiff ℝ N (fun y : ℝ => a*y+c) := by fun_prop
  exact hc.contDiffAt.congr_of_eventuallyEq he

end BfgsVerification.LScalarStep
