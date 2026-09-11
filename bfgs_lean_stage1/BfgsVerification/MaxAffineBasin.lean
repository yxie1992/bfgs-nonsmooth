import Mathlib.Data.EReal.Basic
import BfgsVerification.CenteredRecentering
import BfgsVerification.HomogeneousLowRankRestriction

/-! F:active and F:basin. Actual finite max-affine reduction, literal extended-real
threshold, and accepted-run convergence. No regularity of the max is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace MaxAffine

structure Family (n m : ℕ) where
  a : Fin m → Vec n
  b : Fin m → ℝ
  nonempty : Nonempty (Fin m)

namespace Family
variable {n m : ℕ} (P : Family n m)

include P in
theorem indices_nonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
  obtain ⟨i⟩ := P.nonempty
  exact ⟨i, Finset.mem_univ i⟩

def branch (i : Fin m) (x : Vec n) : ℝ := dot (P.a i) x+P.b i

def objective (x : Vec n) : ℝ := Finset.univ.sup' P.indices_nonempty (fun i => P.branch i x)

theorem branch_le (i : Fin m) (x : Vec n) : P.branch i x ≤ P.objective x :=
  Finset.le_sup' (fun i => P.branch i x) (Finset.mem_univ i)

theorem exists_active (x : Vec n) : ∃ i, P.branch i x = P.objective x := by
  obtain ⟨i, _hi, hv⟩ := Finset.exists_mem_eq_sup' P.indices_nonempty (fun i => P.branch i x)
  exact ⟨i, hv.symm⟩

def activeIndices (star : Vec n) : Finset (Fin m) :=
  Finset.univ.filter (fun i => P.branch i star = P.objective star)

theorem activeIndices_nonempty (star : Vec n) : (P.activeIndices star).Nonempty := by
  obtain ⟨i, hi⟩ := P.exists_active star
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

def activeGauge (star z : Vec n) : ℝ :=
  (P.activeIndices star).sup' (P.activeIndices_nonempty star) (fun i => dot (P.a i) z)

theorem branch_continuous (i : Fin m) : Continuous (P.branch i) :=
  by simpa only [branch, gradientFunctional_apply] using
    ((gradientFunctional (P.a i)).continuous.add (show Continuous (fun _ : Vec n => P.b i) from continuous_const))

theorem branch_translate (i : Fin m) (star z : Vec n) :
    P.branch i (star+z) = P.branch i star+dot (P.a i) z := by
  simp only [branch, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- Every inactive branch is strictly dominated by a fixed active branch on a
neighborhood. No division by slope differences or nonparallelism is used. -/
theorem inactive_eventually_dominated (star : Vec n) :
    ∃ i₀ ∈ P.activeIndices star, ∀ᶠ x in 𝓝 star,
      ∀ j, j ∉ P.activeIndices star → P.branch j x < P.branch i₀ x := by
  obtain ⟨i₀, hi₀⟩ := P.activeIndices_nonempty star
  have hv : P.branch i₀ star = P.objective star := (Finset.mem_filter.mp hi₀).2
  refine ⟨i₀, hi₀, ?_⟩
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : j ∈ P.activeIndices star
  · exact Eventually.of_forall (fun _ hn => (hn hj).elim)
  have hn : P.branch j star ≠ P.objective star := by
    intro he
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, he⟩)
  have hs : P.branch j star < P.branch i₀ star := by
    rw [hv]
    exact lt_of_le_of_ne (P.branch_le j star) hn
  have he : ∀ᶠ x in 𝓝 star, P.branch j x < P.branch i₀ x := (isOpen_lt (P.branch_continuous j) (P.branch_continuous i₀)).mem_nhds hs
  exact he.mono (fun _ h _ => h)

/-- The literal F:active local identity, with the actual active slope maximum. -/
theorem local_active_identity (star : Vec n) :
    P.objective =ᶠ[𝓝 star] (fun x => P.objective star+P.activeGauge star (x-star)) := by
  obtain ⟨i₀, hi₀, hdom⟩ := P.inactive_eventually_dominated star
  filter_upwards [hdom] with x hx
  have ha (i : Fin m) (hi : i ∈ P.activeIndices star) :
      P.branch i x = P.objective star+dot (P.a i) (x-star) := by
    have h := P.branch_translate i star (x-star)
    rw [add_sub_cancel] at h
    exact h.trans (by rw [(Finset.mem_filter.mp hi).2])
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    by_cases hi : i ∈ P.activeIndices star
    · rw [ha i hi]
      exact add_le_add_left (Finset.le_sup' (fun i => dot (P.a i) (x-star)) hi) _
    · exact (hx i hi).le.trans (by
        rw [ha i₀ hi₀]
        exact add_le_add_left (Finset.le_sup' (fun i => dot (P.a i) (x-star)) hi₀) _)
  · rw [add_comm, ← le_sub_iff_add_le]
    apply Finset.sup'_le
    intro i hi
    have hb := P.branch_le i x
    rw [ha i hi] at hb
    linarith


theorem objective_convex : ConvexOn ℝ univ P.objective := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  apply Finset.sup'_le
  intro i _
  have he : P.branch i (a • x+b • z) = a*P.branch i x+b*P.branch i z := by
    unfold branch
    change (P.a i) ⬝ᵥ (a • x+b • z) + P.b i = _
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul, dot, dotProduct] at hab ⊢
    nlinarith [congrArg (fun t : ℝ => t*P.b i) hab]
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left (P.branch_le i x) ha)
    (mul_le_mul_of_nonneg_left (P.branch_le i z) hb)

theorem objective_continuous : Continuous P.objective := convex_continuous P.objective_convex

theorem activeGauge_convex (star : Vec n) : ConvexOn ℝ univ (P.activeGauge star) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  apply Finset.sup'_le
  intro i hi
  change (P.a i) ⬝ᵥ (a • x+b • z) ≤ _
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i => dot (P.a i) x) hi) ha)
    (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i => dot (P.a i) z) hi) hb)

theorem activeGauge_homogeneous (star : Vec n) : Homogeneous.PositiveDegreeOne (P.activeGauge star) := by
  intro t ht x
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    rw [dot_smul_right]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i => dot (P.a i) x) hi) ht
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' (P.activeIndices_nonempty star) (fun i => dot (P.a i) x)
    change t*P.activeGauge star x ≤ _
    rw [show P.activeGauge star x = dot (P.a i) x from he, ← dot_smul_right]
    exact Finset.le_sup' (fun i => dot (P.a i) (t • x)) hi

def activeRegion (i : Fin m) : Set (Vec n) := {x | P.branch i x = P.objective x}

theorem activeRegion_closed (i : Fin m) : IsClosed (P.activeRegion i) :=
  isClosed_eq (P.branch_continuous i) P.objective_continuous

/-- The actual closed active region is exactly the stated finite system of
linear inequalities, including parallel or identical pieces. -/
theorem activeRegion_iff (i : Fin m) (x : Vec n) :
    x ∈ P.activeRegion i ↔ ∀ j, dot (P.a j-P.a i) x ≤ P.b i-P.b j := by
  constructor
  · intro hx j
    have hh := P.branch_le j x
    change P.branch i x = P.objective x at hx
    rw [← hx] at hh
    simp only [branch] at hh
    rw [dot_sub_left]
    linarith
  · intro hx
    change P.branch i x = P.objective x
    apply le_antisymm (P.branch_le i x)
    apply Finset.sup'_le
    intro j _
    have hh := hx j
    rw [dot_sub_left] at hh
    unfold branch
    linarith

theorem inactive_center_not_mem (star : Vec n) {i : Fin m} (hi : i ∉ P.activeIndices star) :
    star ∉ P.activeRegion i := by
  intro hx
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩)


/-- Adding a constant preserves the original local C1,1 condition. -/
theorem locallyC11_add_const {ψ : Vec n → ℝ} {U : Set (Vec n)}
    (hU : IsOpen U) (hs : CenteredSmoothSublinear.LocallyC11On U ψ) (c : ℝ) :
    CenteredSmoothSublinear.LocallyC11On U (fun x => ψ x+c) := by
  have hd : ∀ x ∈ U, HasFDerivAt (fun x => ψ x+c) (fderiv ℝ ψ x) x := by
    intro x hx
    exact (((hs.1 x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt).add_const c
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_⟩
  intro x hx
  obtain ⟨M,V,hV,hLip⟩ := hs.2 hx
  refine ⟨M,V ∩ U,inter_mem hV self_mem_nhdsWithin, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro a ha b hb
  rw [(hd a ha.2).fderiv,(hd b hb.2).fderiv]
  exact hLip.dist_le_mul a ha.1 b hb.1

/-- The actual max-affine objective has a basin at its unique minimizer,
quantified before every admissible run and every initial positive metric. -/
theorem local_basin {ψ : Vec n → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hs : CenteredSmoothSublinear.LocallyC11On univ ψ) (star : Vec n)
    (hmin : ∀ x, ψ star+P.objective star ≤ ψ x+P.objective x)
    (hu : ∀ x, ψ x+P.objective x = ψ star+P.objective star → x=star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n (fun x => ψ x+P.objective x),
      ψ (R.x 0)+P.objective (R.x 0) ≤ ψ star+P.objective star+δ →
      Tendsto (fun k => ψ (R.x k)+P.objective (R.x k)) atTop (𝓝 (ψ star+P.objective star)) ∧
        Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (P.local_active_identity star)
  let U := Metric.ball star ε
  have hU : IsOpen U := Metric.isOpen_ball
  have hstar : star ∈ U := Metric.mem_ball_self hε
  have hsub : U ⊆ univ := subset_univ _
  have hsU : CenteredSmoothSublinear.LocallyC11On U ψ := ⟨hs.1.mono hsub,hs.2.mono hsub⟩
  have hrep : ∀ x ∈ U, ψ x+P.objective x =
      (ψ x+P.objective star)+P.activeGauge star (x-star) := by
    intro x hx
    have he := hball hx
    change P.objective x = P.objective star+P.activeGauge star (x-star) at he
    rw [he]
    ring
  obtain ⟨δ,hδ,hb⟩ := CenteredSmoothSublinear.local_centered_basin
    (hψ.add P.objective_convex) star hmin hu hU hstar
    ((hψ.add_const (P.objective star)).subset hsub (convex_ball star ε))
    (locallyC11_add_const hU hsU _) (P.activeGauge_convex star)
    (P.activeGauge_homogeneous star) hrep
  exact ⟨δ,hδ,fun R hstart => (hb R hstart).2⟩


/-- Union of the actual closed active regions of indices inactive at star. -/
def badRegion (star : Vec n) : Set (Vec n) :=
  ⋃ i : {i : Fin m // i ∉ P.activeIndices star}, P.activeRegion i.val

theorem badRegion_closed (star : Vec n) : IsClosed (P.badRegion star) := by
  classical
  exact isClosed_iUnion_of_finite (fun i => P.activeRegion_closed i.val)

theorem center_not_badRegion (star : Vec n) : star ∉ P.badRegion star := by
  intro hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  exact P.inactive_center_not_mem star i.property hi

theorem active_identity_outside_badRegion (star x : Vec n) (hx : x ∉ P.badRegion star) :
    P.objective x = P.objective star+P.activeGauge star (x-star) := by
  have ha (i : Fin m) (hi : i ∈ P.activeIndices star) :
      P.branch i x = P.objective star+dot (P.a i) (x-star) := by
    have he := P.branch_translate i star (x-star)
    rw [add_sub_cancel] at he
    exact he.trans (by rw [(Finset.mem_filter.mp hi).2])
  apply le_antisymm
  · obtain ⟨i,hi⟩ := P.exists_active x
    have histar : i ∈ P.activeIndices star := by
      by_contra hn
      exact hx (mem_iUnion.mpr ⟨⟨i,hn⟩,hi⟩)
    rw [← hi,ha i histar]
    exact add_le_add_left (Finset.le_sup' (fun i => dot (P.a i) (x-star)) histar) _
  · rw [add_comm, ← le_sub_iff_add_le]
    apply Finset.sup'_le
    intro i hi
    have hb := P.branch_le i x
    rw [ha i hi] at hb
    linarith

/-- Literal extended-real level threshold. The empty bad region has threshold
+infinity, using the complete-lattice infimum rather than a real infimum. -/
def threshold (F : Vec n → ℝ) (star : Vec n) : EReal :=
  sInf ((fun x => (F x : EReal)) '' P.badRegion star)

theorem threshold_empty {F : Vec n → ℝ} {star : Vec n} (he : P.badRegion star = ∅) :
    P.threshold F star = ⊤ := by simp [threshold,he]

theorem below_threshold_not_bad {F : Vec n → ℝ} {star x : Vec n}
    (hx : (F x : EReal) < P.threshold F star) : x ∉ P.badRegion star := by
  intro hb
  have hh : P.threshold F star ≤ (F x : EReal) := sInf_le (mem_image_of_mem _ hb)
  exact (not_lt_of_ge hh) hx

/-- Compact sublevels make the minimum on every nonempty closed set attained. -/
theorem exists_min_on_closed {F : Vec n → ℝ} (hF : Continuous F)
    (hsub : ∀ b : ℝ, IsCompact {x | F x ≤ b}) {K : Set (Vec n)}
    (hK : IsClosed K) (hne : K.Nonempty) : ∃ z ∈ K, ∀ x ∈ K, F z ≤ F x := by
  obtain ⟨x₀,hx₀⟩ := hne
  have hC : IsCompact (K ∩ {x | F x ≤ F x₀}) := (hsub (F x₀)).inter_left hK
  obtain ⟨z,hz,hm⟩ := hC.exists_isMinOn ⟨x₀,hx₀,show F x₀ ≤ F x₀ from le_rfl⟩ hF.continuousOn
  refine ⟨z,hz.1,?_⟩
  intro x hx
  by_cases hfx : F x ≤ F x₀
  · exact hm ⟨hx,hfx⟩
  · exact hz.2.trans (le_of_not_ge hfx)

/-- A nonempty inactive region has a finite attained threshold. -/
theorem threshold_attained {F : Vec n → ℝ} (hF : Continuous F)
    (hsub : ∀ b : ℝ, IsCompact {x | F x ≤ b}) (star : Vec n)
    (hne : (P.badRegion star).Nonempty) :
    ∃ z ∈ P.badRegion star, P.threshold F star = (F z : EReal) := by
  obtain ⟨z,hz,hm⟩ := exists_min_on_closed hF hsub (P.badRegion_closed star) hne
  refine ⟨z,hz,le_antisymm (sInf_le (mem_image_of_mem _ hz)) ?_⟩
  apply le_sInf
  rintro _ ⟨x,hx,rfl⟩
  exact EReal.coe_le_coe_iff.mpr (hm x hx)

/-- The extended-real threshold strictly exceeds the unique minimum, including
empty inactive regions and all parallel-piece degeneracies. -/
theorem threshold_gt_minimum {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (star : Vec n) (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x=star) :
    (F star : EReal) < P.threshold F star := by
  by_cases hne : (P.badRegion star).Nonempty
  · obtain ⟨z,hz,he⟩ := P.threshold_attained (convex_continuous hF)
      (fun b => Localization.sublevel_compact hF star hmin hu b) star hne
    rw [he]
    apply EReal.coe_lt_coe_iff.mpr
    apply lt_of_le_of_ne (hmin z)
    intro hv
    have hx := hu z hv.symm
    exact P.center_not_badRegion star (hx ▸ hz)
  · rw [P.threshold_empty (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact EReal.coe_lt_top _


/-- This is the source minimum of the inactive-region infima, with empty
index sets or empty active regions assigned +infinity. -/
theorem threshold_eq_inactive_infima (F : Vec n → ℝ) (star : Vec n) :
    P.threshold F star = ⨅ i : {i : Fin m // i ∉ P.activeIndices star},
      sInf ((fun x => (F x : EReal)) '' P.activeRegion i.val) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    apply le_sInf
    rintro _ ⟨x,hx,rfl⟩
    exact sInf_le (mem_image_of_mem _ (mem_iUnion.mpr ⟨i,hx⟩))
  · apply le_sInf
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact iInf_le_of_le i (sInf_le (mem_image_of_mem _ hi))

/-- Every start strictly below the literal inactive-region threshold converges.
A strictly larger sublevel below that threshold supplies an open convex
representation neighborhood for the full compact initial sublevel. -/
theorem threshold_convergence {ψ : Vec n → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hs : CenteredSmoothSublinear.LocallyC11On univ ψ) (star : Vec n)
    (hmin : ∀ x, ψ star+P.objective star ≤ ψ x+P.objective x)
    (hu : ∀ x, ψ x+P.objective x = ψ star+P.objective star → x=star)
    (R : AdmissibleBFGSRun n (fun x => ψ x+P.objective x))
    (hstart : ((ψ (R.x 0)+P.objective (R.x 0) : ℝ) : EReal) <
      P.threshold (fun x => ψ x+P.objective x) star) :
    Tendsto (fun k => ψ (R.x k)+P.objective (R.x k)) atTop (𝓝 (ψ star+P.objective star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  let F := fun x => ψ x+P.objective x
  obtain ⟨b,hb0,hbt⟩ := EReal.exists_between_coe_real hstart
  have hFb : F (R.x 0) < b := EReal.coe_lt_coe_iff.mp hb0
  let U := {x | F x < b}
  have hF : ConvexOn ℝ univ F := hψ.add P.objective_convex
  have hU : IsOpen U := isOpen_lt (convex_continuous hF) continuous_const
  have hUc : Convex ℝ U := by simpa only [mem_univ, true_and] using hF.convex_lt b
  have hsub : U ⊆ univ := subset_univ _
  have hsU : CenteredSmoothSublinear.LocallyC11On U ψ := ⟨hs.1.mono hsub,hs.2.mono hsub⟩
  have hrep : ∀ x ∈ U, F x = (ψ x+P.objective star)+P.activeGauge star (x-star) := by
    intro x hx
    have he := P.active_identity_outside_badRegion star x
      (P.below_threshold_not_bad ((EReal.coe_lt_coe_iff.mpr hx).trans hbt))
    dsimp only [F]
    rw [he]
    ring
  have hK := R.initialSublevel_compact_of_unique_minimizer star hmin hu
  have hKU : R.initialSublevel ⊆ U := fun x hx => hx.trans_lt hFb
  have hv := R.centered_values star hmin hU ((hψ.add_const (P.objective star)).subset hsub hUc)
    (locallyC11_add_const hU hsU _) (P.activeGauge_convex star)
    (P.activeGauge_homogeneous star) hrep hK hKU
  exact ⟨hv,R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

/-- A run which enters the certified level after a finite prefix converges with
its actual current metric; no restart or algorithm modification is performed. -/
theorem threshold_tail_convergence {ψ : Vec n → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hs : CenteredSmoothSublinear.LocallyC11On univ ψ) (star : Vec n)
    (hmin : ∀ x, ψ star+P.objective star ≤ ψ x+P.objective x)
    (hu : ∀ x, ψ x+P.objective x = ψ star+P.objective star → x=star)
    (R : AdmissibleBFGSRun n (fun x => ψ x+P.objective x)) (J : ℕ)
    (hstart : ((ψ (R.x J)+P.objective (R.x J) : ℝ) : EReal) <
      P.threshold (fun x => ψ x+P.objective x) star) :
    Tendsto (fun k => ψ (R.x k)+P.objective (R.x k)) atTop (𝓝 (ψ star+P.objective star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  have ht := P.threshold_convergence hψ hs star hmin hu (R.shift J) hstart
  constructor
  · apply (tendsto_add_atTop_iff_nat J).mp
    simpa only [AdmissibleBFGSRun.shift, Nat.add_comm] using ht.1
  · apply (tendsto_add_atTop_iff_nat J).mp
    simpa only [AdmissibleBFGSRun.shift, Nat.add_comm] using ht.2


theorem inactive_gap_pos (star : Vec n) {j : Fin m} (hj : j ∉ P.activeIndices star) :
    0 < P.objective star-P.branch j star := by
  apply sub_pos.mpr
  apply lt_of_le_of_ne (P.branch_le j star)
  intro he
  exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j,he⟩)

/-- The printed Euclidean radius formula for one inactive nonparallel piece. -/
theorem inactive_radius_domination (star z : Vec n) {i j : Fin m}
    (hi : i ∈ P.activeIndices star) (hj : j ∉ P.activeIndices star)
    (hij : P.a i ≠ P.a j)
    (hz : ‖euclideanVector z‖ ≤ (P.objective star-P.branch j star)/
      (2*‖euclideanVector (P.a i-P.a j)‖)) :
    P.branch j (star+z) < P.branch i (star+z) := by
  have hg := P.inactive_gap_pos star hj
  have hv : euclideanVector (P.a i-P.a j) ≠ 0 := by
    intro he
    apply hij
    apply sub_eq_zero.mp
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => fun k => v k) he
  have hA : 0 < ‖euclideanVector (P.a i-P.a j)‖ := norm_pos_iff.mpr hv
  have hsq (v : Vec n) : sqNorm v ≤ ‖euclideanVector v‖^2 :=
    le_of_eq (FrameNorms.euclidean_norm_sq (euclideanVector v)).symm
  have hc := abs_dot_le_of_sqNorm_le (P.a i-P.a j) z _ _ (norm_nonneg _) (norm_nonneg _) (hsq _) (hsq _)
  have hrad := (le_div_iff₀ (show 0 < 2*‖euclideanVector (P.a i-P.a j)‖ by positivity)).mp hz
  rw [P.branch_translate, P.branch_translate, (Finset.mem_filter.mp hi).2]
  rw [dot_sub_left] at hc
  nlinarith [(abs_le.mp (hc.trans (show ‖euclideanVector (P.a i-P.a j)‖*‖euclideanVector z‖ ≤
    (P.objective star-P.branch j star)/2 by nlinarith))).1]

/-- A parallel inactive piece stays strictly dominated everywhere. -/
theorem parallel_inactive_domination (star z : Vec n) {i j : Fin m}
    (hi : i ∈ P.activeIndices star) (hj : j ∉ P.activeIndices star)
    (hij : P.a i = P.a j) : P.branch j (star+z) < P.branch i (star+z) := by
  have hg := P.inactive_gap_pos star hj
  rw [P.branch_translate, P.branch_translate, (Finset.mem_filter.mp hi).2, hij]
  linarith


/-- Each inner threshold problem has an actual convex feasible region. -/
theorem activeRegion_convex (i : Fin m) : Convex ℝ (P.activeRegion i) := by
  intro x hx z hz a b ha hb hab
  apply (P.activeRegion_iff i _).mpr
  intro j
  have h1 := (P.activeRegion_iff i x).mp hx j
  have h2 := (P.activeRegion_iff i z).mp hz j
  have hh := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  change (P.a j-P.a i) ⬝ᵥ (a • x+b • z) ≤ _
  rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
  simp only [dot,dotProduct,smul_eq_mul] at hh ⊢
  nlinarith [congrArg (fun t : ℝ => t*(P.b i-P.b j)) hab]

end Family
end MaxAffine
end BfgsVerification
