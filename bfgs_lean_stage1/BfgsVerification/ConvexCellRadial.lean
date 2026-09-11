import BfgsVerification.PoweredGaugeRadial

/-! Inward radial estimates for finite closed convex cells with local C1,1
extensions. The proof identifies only the radial derivative at a cell boundary. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.ConvexCellRadial

theorem inward_mem {n : ℕ} {P : Set (Vec n)} (hP : Convex ℝ P)
    {star x : Vec n} (hs : star ∈ P) (hx : x ∈ P) {t : ℝ} (ht : t ∈ Icc 0 1) :
    RadialCertificate.inwardPoint star x t ∈ P := by
  have he : RadialCertificate.inwardPoint star x t = (1-t) • x+t • star := by
    unfold RadialCertificate.inwardPoint
    module
  rw [he]
  exact hP hx hs (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- Equality on the inward cell segment identifies the radial derivative even
at a lower-dimensional cell or a nondifferentiable interface of the pieces. -/
theorem radial_derivative_eq {n : ℕ} {F f : Vec n → ℝ} {P U : Set (Vec n)}
    (hP : Convex ℝ P) (hU : Convex ℝ U) {star x g : Vec n}
    (hsP : star ∈ P) (hxP : x ∈ P) (hsU : star ∈ U) (hxU : x ∈ U)
    (hrep : ∀ z ∈ U, z ∈ P → F z = f z)
    (hg : HasFDerivAt F (gradientFunctional g) x) (hf : DifferentiableAt ℝ f x) :
    dot g (x-star) = (fderiv ℝ f x) (x-star) := by
  have hcurve : HasDerivAt (fun t => RadialCertificate.inwardPoint star x t) (-(x-star)) 0 := by
    simpa only [RadialCertificate.inwardPoint,one_smul,zero_sub] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (x-star)).const_sub x
  have hdF := hg.comp_hasDerivAt_of_eq 0 hcurve (by simp [RadialCertificate.inwardPoint])
  have hdf := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp [RadialCertificate.inwardPoint])
  have heq : (fun t => F (RadialCertificate.inwardPoint star x t)) =ᶠ[𝓝[Icc 0 1] 0]
      (fun t => f (RadialCertificate.inwardPoint star x t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hrep _ (inward_mem hU hsU hxU ht) (inward_mem hP hsP hxP ht)
  have hu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
    uniqueDiffOn_Icc (by norm_num) 0 (by constructor <;> norm_num)
  have hd := hu.eq_deriv _ hdF.hasDerivWithinAt
    (hdf.hasDerivWithinAt.congr_of_eventuallyEq heq (by simpa [RadialCertificate.inwardPoint] using hrep x hxU hxP))
  simp only [gradientFunctional_apply,map_neg] at hd
  linarith

theorem finite_incident_cells_inward {n : ℕ} {ι : Type*} [Fintype ι]
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (P : ι → Set (Vec n))
    (f : ι → Vec n → ℝ) (hP : ∀ i, Convex ℝ (P i))
    {star : Vec n} (hsP : ∀ i, star ∈ P i) {U K : Set (Vec n)}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hsU : star ∈ U)
    (hsmooth : ∀ i, CenteredSmoothSublinear.LocallyC11On U (f i))
    (hK : IsCompact K) (hKU : K ⊆ U) (hcover : ∀ x ∈ K, ∃ i, x ∈ P i)
    (hrep : ∀ i x, x ∈ U → x ∈ P i → F x = f i x) :
    RadialCertificate.HasInwardTaylorBounds F K star := by
  classical
  choose D θ hD hθ hθhalf hb using fun i =>
    RadialPower.uniform_smooth_inward_remainder hU (hsmooth i) hK hKU star
  obtain ⟨e,he,heθ⟩ := CenteredSmoothSublinear.finite_positive_lower_bound Finset.univ θ
    (fun i _ => hθ i)
  let e' := min e (1/2)
  have he' : 0 < e' := lt_min he (by norm_num)
  intro η hη
  refine ⟨2*(∑ i, D i),e',he',min_le_right _ _,?_⟩
  intro x g hx _ hg t ht hte
  obtain ⟨i,hxi⟩ := hcover x hx
  have hti : t ≤ θ i := (hte.trans (min_le_left _ _)).trans (heθ i (Finset.mem_univ i))
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht, hti.trans ((hθhalf i).trans (by norm_num))⟩
  have hdiff := ((hsmooth i).1 x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  have hd := radial_derivative_eq (hP i) hUc (hsP i) hxi hsU (hKU hx) (hrep i) hg hdiff
  have hbound := (hb i x hx t ht hti).2
  have hs := Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)
  refine ⟨RadialCertificate.supportingError_nonneg hF hg _,?_⟩
  rw [RadialCertificate.inward_error_eq,hd,hrep i x (hKU hx) hxi,
    hrep i _ (inward_mem hUc hsU (hKU hx) htc) (inward_mem (hP i) (hsP i) hxi htc)]
  have hh := (le_abs_self _).trans hbound
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
  nlinarith

/-- Finiteness and closedness discard nonincident cells, while each incident
extension supplies its own open neighborhood. No common extension domain is
assumed before shrinking. -/
theorem incident_neighborhood {n : ℕ} {ι : Type*} [Fintype ι]
    (P V : ι → Set (Vec n)) (hP : ∀ i, IsClosed (P i)) (hV : ∀ i, IsOpen (V i))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hpart : ∀ i, U ∩ P i ⊆ V i) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball star ε ⊆ U ∧
      (∀ i x, x ∈ Metric.ball star ε → x ∈ P i → star ∈ P i) ∧
      (∀ i, star ∈ P i → Metric.ball star ε ⊆ V i) := by
  have he (i : ι) : ∀ᶠ x in 𝓝 star,
      (x ∈ P i → star ∈ P i) ∧ (star ∈ P i → x ∈ V i) := by
    by_cases hi : star ∈ P i
    · filter_upwards [(hV i).mem_nhds (hpart i ⟨hsU,hi⟩)] with x hx
      exact ⟨fun _ => hi,fun _ => hx⟩
    · filter_upwards [(hP i).isOpen_compl.mem_nhds hi] with x hx
      exact ⟨fun hxp => (hx hxp).elim,fun hs => (hi hs).elim⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hsU) (Filter.eventually_all.mpr he))
  exact ⟨ε,hε,fun x hx => (hball hx).1,
    fun i x hx => ((hball hx).2 i).1,fun i hi x hx => ((hball hx).2 i).2 hi⟩

/-- A finite closed convex cell representation with separate local C1,1
extensions gives IR on every compact subset of one fixed neighborhood. Only
the full objective must be convex; extensions need not be convex off cells. -/
theorem local_cells_inward {n : ℕ} {ι : Type*} [Fintype ι]
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (P V : ι → Set (Vec n)) (f : ι → Vec n → ℝ)
    (hPc : ∀ i, IsClosed (P i)) (hPv : ∀ i, Convex ℝ (P i))
    (hV : ∀ i, IsOpen (V i))
    (hsmooth : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hpart : ∀ i, U ∩ P i ⊆ V i) (hcover : ∀ x ∈ U, ∃ i, x ∈ P i)
    (hrep : ∀ i x, x ∈ U → x ∈ P i → F x = f i x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ K : Set (Vec n), IsCompact K → K ⊆ Metric.ball star ε →
      RadialCertificate.HasInwardTaylorBounds F K star := by
  classical
  obtain ⟨ε,hε,hBU,hinc,hBV⟩ := incident_neighborhood P V hPc hV hU hsU hpart
  refine ⟨ε,hε,?_⟩
  intro K hK hKB
  let J := {i : ι // star ∈ P i}
  have hsm (i : J) : CenteredSmoothSublinear.LocallyC11On (Metric.ball star ε) (f i.val) :=
    ⟨(hsmooth i.val).1.mono (hBV i.val i.property),
      (hsmooth i.val).2.mono (hBV i.val i.property)⟩
  apply finite_incident_cells_inward hF (fun i : J => P i.val) (fun i : J => f i.val)
    (fun i => hPv i.val) (fun i => i.property) Metric.isOpen_ball (convex_ball star ε)
    (Metric.mem_ball_self hε) hsm hK hKB
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x (hBU (hKB hx))
    exact ⟨⟨i,hinc i x (hKB hx) hi⟩,hi⟩
  · intro i x hx hxi
    exact hrep i.val x (hBU hx) hxi

/-- Exact local convergence consequence for every actual admissible full-BFGS
run, with a basin selected before the run or its initial SPD matrix. -/
theorem local_cells_basin {n : ℕ} {ι : Type*} [Fintype ι]
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (P V : ι → Set (Vec n)) (f : ι → Vec n → ℝ)
    (hPc : ∀ i, IsClosed (P i)) (hPv : ∀ i, Convex ℝ (P i))
    (hV : ∀ i, IsOpen (V i))
    (hsmooth : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hpart : ∀ i, U ∩ P i ⊆ V i) (hcover : ∀ x ∈ U, ∃ i, x ∈ P i)
    (hrep : ∀ i x, x ∈ U → x ∈ P i → F x = f i x)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  obtain ⟨ε,hε,hIR⟩ := local_cells_inward hF P V f hPc hPv hV hsmooth hU hsU hpart hcover hrep
  obtain ⟨δ,hδ,hsub⟩ := Localization.neighborhood_basin hF star hmin hu
    (inter_mem (Metric.ball_mem_nhds star hε) (hU.mem_nhds hsU))
  refine ⟨δ,hδ,?_⟩
  intro R hstart
  have hK := R.initialSublevel_compact_of_unique_minimizer star hmin hu
  have hKB : R.initialSublevel ⊆ Metric.ball star ε := fun x hx => (hsub (hx.trans hstart)).1
  have hKU : R.initialSublevel ⊆ U := fun x hx => (hsub (hx.trans hstart)).2
  have hrs := RadialCertificate.radial_of_inward_on_compact hF hK star (hIR _ hK hKB)
  have hv := R.radial_certificate_values _ hK R.iterate_mem_initialSublevel star hmin hrs
  exact ⟨fun k => hKU (R.iterate_mem_initialSublevel k),hv,
    R.iterates_tendsto_unique_min_of_values star hmin hu hv⟩

/-- Actual closed polyhedron given by finitely many affine halfspaces. Empty
constraint sets represent the entire ambient space. -/
def polyhedron {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ) : Set (Vec n) :=
  {x | ∀ j, dot (a j) x ≤ b j}

theorem polyhedron_closed {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ) :
    IsClosed (polyhedron a b) := by
  have he : polyhedron a b = ⋂ j, {x | dot (a j) x ≤ b j} := by
    ext x
    simp [polyhedron]
  rw [he]
  apply isClosed_iInter
  intro j
  have hc : Continuous (dot (a j)) := by
    convert (gradientFunctional (a j)).continuous using 1
    funext x
    exact (gradientFunctional_apply (a j) x).symm
  exact isClosed_le hc continuous_const

theorem polyhedron_convex {n m : ℕ} (a : Fin m → Vec n) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron a b) := by
  intro x hx y hy α β hα hβ hsum j
  have he : dot (a j) (α • x+β • y) = α*dot (a j) x+β*dot (a j) y := by
    simp only [dot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
  rw [he]
  have hb := add_le_add (mul_le_mul_of_nonneg_left (hx j) hα)
    (mul_le_mul_of_nonneg_left (hy j) hβ)
  nlinarith [congrArg (fun t : ℝ => t*b j) hsum]

/-- The literal finite-polyhedral-partition hypothesis, with actual affine
inequality cells and separate smooth extension neighborhoods, implies the
source's local full-BFGS convergence conclusion. Full dimensionality and
disjoint cell interiors are unnecessary for this stronger radial proof. -/
theorem finite_polyhedral_basin {n : ℕ} {ι : Type*} [Fintype ι] {m : ι → ℕ}
    {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F)
    (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (V : ι → Set (Vec n)) (f : ι → Vec n → ℝ)
    (hV : ∀ i, IsOpen (V i))
    (hsmooth : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    {U : Set (Vec n)} (hU : IsOpen U) {star : Vec n} (hsU : star ∈ U)
    (hpart : ∀ i, U ∩ polyhedron (a i) (b i) ⊆ V i)
    (hcover : ∀ x ∈ U, ∃ i, x ∈ polyhedron (a i) (b i))
    (hrep : ∀ i x, x ∈ U → x ∈ polyhedron (a i) (b i) → F x = f i x)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x = F star → x = star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) :=
  local_cells_basin hF (fun i => polyhedron (a i) (b i)) V f
    (fun i => polyhedron_closed (a i) (b i)) (fun i => polyhedron_convex (a i) (b i))
    hV hsmooth hU hsU hpart hcover hrep hmin hu

end BfgsVerification.ConvexCellRadial
