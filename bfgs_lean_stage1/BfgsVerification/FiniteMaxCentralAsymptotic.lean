import BfgsVerification.FiniteMaxRadialSufficiency
import BfgsVerification.FiniteMaxRadialObstruction

/-! Literal central J|t|+O(t²) expansion for actual finite smooth maxima.
Completed after the seventh milestone; built and audited independently before integration. -/
noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter
namespace BfgsVerification.FiniteMaxRadial

theorem finite_max_taylor_positive {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    (f d : ι → ℝ) (b t E : ℝ) (ht : 0 ≤ t)
    (hrem : ∀ i ∈ s, |f i-b-t*d i| ≤ E) :
    |s.sup' hne f-b-t*s.sup' hne d| ≤ E := by
  apply abs_le.mpr
  constructor
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' hne d
    have hlo := (abs_le.mp (hrem i hi)).1
    have hfi := Finset.le_sup' f hi
    rw [he]
    linarith
  · have hup : s.sup' hne f ≤ b+t*s.sup' hne d+E := by
      apply Finset.sup'_le
      intro i hi
      have hd := mul_le_mul_of_nonneg_left (Finset.le_sup' d hi) ht
      have hfi := (abs_le.mp (hrem i hi)).2
      linarith
    linarith

theorem finite_max_taylor_negative {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    (f d : ι → ℝ) (b t E : ℝ) (ht : 0 ≤ t)
    (hrem : ∀ i ∈ s, |f i-b+t*d i| ≤ E) :
    |s.sup' hne f-b+t*s.inf' hne d| ≤ E := by
  apply abs_le.mpr
  constructor
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hne d
    have hlo := (abs_le.mp (hrem i hi)).1
    have hfi := Finset.le_sup' f hi
    rw [he]
    linarith
  · have hup : s.sup' hne f ≤ b-t*s.inf' hne d+E := by
      apply Finset.sup'_le
      intro i hi
      have hd := mul_le_mul_of_nonneg_left (Finset.inf'_le d hi) ht
      have hfi := (abs_le.mp (hrem i hi)).2
      linarith
    linarith

theorem finite_max_central_positive {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (d : ι → ℝ) (b t E : ℝ) (ht : 0 ≤ t)
    (hp : ∀ i ∈ s, |f i t-b-t*d i| ≤ E)
    (hn : ∀ i ∈ s, |f i (-t)-b+t*d i| ≤ E) :
    |maximum s hne f t+maximum s hne f (-t)-2*b-
      (s.sup' hne d-s.inf' hne d)*t| ≤ 2*E := by
  have hh := finite_max_taylor_positive hne (fun i => f i t) d b t E ht hp
  have hl := finite_max_taylor_negative hne (fun i => f i (-t)) d b t E ht hn
  rw [abs_le] at hh hl ⊢
  simp only [maximum]
  constructor <;> linarith

theorem finite_max_central_absolute {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    (f : ι → ℝ → ℝ) (d : ι → ℝ) (b t C : ℝ)
    (hp : ∀ i ∈ s, |f i t-b-t*d i| ≤ C*t^2)
    (hn : ∀ i ∈ s, |f i (-t)-b-(-t)*d i| ≤ C*t^2) :
    |maximum s hne f t+maximum s hne f (-t)-2*b-
      (s.sup' hne d-s.inf' hne d)*abs t| ≤ 2*C*t^2 := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have h := finite_max_central_positive hne f d b t (C*t^2) ht hp
      (fun i hi => by simpa using hn i hi)
    convert h using 1 <;> ring
  · rw [abs_of_nonpos ht]
    have h := finite_max_central_positive hne f d b (-t) (C*t^2) (neg_nonneg.mpr ht) hn
      (fun i hi => by simpa using hp i hi)
    simp only [neg_neg] at h
    convert h using 1 <;> ring


/-- C² regularity of the actual branches supplies a common radial quadratic
remainder. No scalar remainder estimate is assumed as a final premise. -/
theorem finite_branch_radial_remainders {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {w : Vec n} (hw : w ∈ U)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) U) (r : Vec n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in 𝓝 0, ∀ i,
      |f i (w+t • r)-f i w-t*(fderiv ℝ (f i) w) r| ≤ C*t^2 := by
  obtain ⟨M,ρ,hρ,hBU,hM⟩ := finite_branch_neighborhood hne f hU hw hf
  have hwb : w ∈ Metric.ball w ρ := Metric.mem_ball_self hρ
  have hdiff (i : ι) (z : Vec n) (hz : z ∈ Metric.ball w ρ) : DifferentiableAt ℝ (f i) z :=
    (((hf i).differentiableOn (by norm_num)) z (hBU hz)).differentiableAt
      (hU.mem_nhds (hBU hz))
  have ht : Tendsto (fun t : ℝ => w+t • r) (𝓝 0) (𝓝 w) := by
    have hc : Continuous (fun t : ℝ => w+t • r) := by fun_prop
    simpa using hc.tendsto 0
  refine ⟨M*sqNorm r,mul_nonneg M.coe_nonneg (sqNorm_nonneg r),?_⟩
  filter_upwards [ht.eventually (Metric.isOpen_ball.mem_nhds hwb)] with t ht
  intro i
  have h := CenteredSmoothSublinear.taylor_remainder_le (convex_ball w ρ)
    (hdiff i) (hM i) hwb ht
  have he : w+t • r-w=t • r := by module
  rw [he,map_smul,smul_eq_mul,RadialPower.sqNorm_smul] at h
  convert h using 1 <;> ring

def activeRadialSet {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ) (w r : Vec n) : Finset ι :=
  activeIndices Finset.univ hne (fun i t => f i (w+t • r)) 0

theorem activeRadialSet_nonempty {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ) (w r : Vec n) :
    (activeRadialSet hne f w r).Nonempty :=
  activeIndices_nonempty Finset.univ hne (fun i t => f i (w+t • r)) 0

def activeRadialJump {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ) (w r : Vec n) : ℝ :=
  (activeRadialSet hne f w r).sup' (activeRadialSet_nonempty hne f w r)
    (fun i => (fderiv ℝ (f i) w) r) -
  (activeRadialSet hne f w r).inf' (activeRadialSet_nonempty hne f w r)
    (fun i => (fderiv ℝ (f i) w) r)

theorem activeRadialJump_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ) (w r : Vec n) :
    0 ≤ activeRadialJump hne f w r := by
  obtain ⟨i,hi⟩ := activeRadialSet_nonempty hne f w r
  unfold activeRadialJump
  exact sub_nonneg.mpr ((Finset.inf'_le (fun i => (fderiv ℝ (f i) w) r) hi).trans
    (Finset.le_sup' (fun i => (fderiv ℝ (f i) w) r) hi))


/-- The exact central expansion for a genuine local finite C² maximum. The
jump coefficient is the full max-minus-min active directional derivative. -/
theorem finite_max_central_remainder {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ} (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {w : Vec n} (hw : w ∈ U)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ z ∈ U, F z=Finset.univ.sup' hne (fun i => f i z)) (r : Vec n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in 𝓝 0,
      |F (w+t • r)+F (w-t • r)-2*F w-activeRadialJump hne f w r*abs t| ≤ C*t^2 := by
  let q : ι → ℝ → ℝ := fun i t => f i (w+t • r)
  let Q := maximum Finset.univ hne q
  let A := activeRadialSet hne f w r
  have hA := activeRadialSet_nonempty hne f w r
  have ht : Tendsto (fun t : ℝ => w+t • r) (𝓝 0) (𝓝 w) := by
    have hc : Continuous (fun t : ℝ => w+t • r) := by fun_prop
    simpa using hc.tendsto 0
  have hqcont (i : ι) : ContinuousAt (q i) 0 := by
    simpa only [ContinuousAt,Function.comp_def,q,zero_smul,add_zero] using
      (((hf i).continuousOn.continuousAt (hU.mem_nhds hw)).tendsto.comp ht)
  have he := maximum_eventually_eq_active hne (fun i _ => hqcont i)
  have heF : ∀ᶠ t : ℝ in 𝓝 0, F (w+t • r)=Q t := by
    filter_upwards [ht.eventually (hU.mem_nhds hw)] with t ht
    exact hrep _ ht
  have hval (i : ι) (hi : i ∈ A) : f i w=F w := by
    have ha : q i 0=Q 0 := (Finset.mem_filter.mp hi).2
    simpa [q,Q,maximum,hrep w hw] using ha
  obtain ⟨C,hC,hrem⟩ := finite_branch_radial_remainders hne f hU hw hf r
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ))
  refine ⟨2*C,mul_nonneg (by norm_num) hC,?_⟩
  filter_upwards [he,heF,hrem,hneg.eventually he,hneg.eventually heF,hneg.eventually hrem]
    with t he heF hp hen heFn hn
  have h := finite_max_central_absolute hA q (fun i => (fderiv ℝ (f i) w) r) (F w) t C
    (fun i hi => by simpa only [q,hval i hi] using hp i)
    (fun i hi => by simpa only [q,hval i hi,neg_sq] using hn i)
  have hminus : w+(-t) • r=w-t • r := by module
  change Q t=maximum A hA q t at he
  change Q (-t)=maximum A hA q (-t) at hen
  rw [← he,← hen,← heF,← heFn,hminus] at h
  exact h

/-- Literal source notation: central difference equals J|t| plus O(t²),
with J computed from every active branch, including ties with more than two branches. -/
theorem finite_max_central_isBigO {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ} (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {w star : Vec n} (hw : w ∈ U)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ z ∈ U, F z=Finset.univ.sup' hne (fun i => f i z)) :
    (fun t : ℝ => RadialCertificate.centralDifference F star w t-
      activeRadialJump hne f w (w-star)*abs t) =O[𝓝 0] (fun t : ℝ => t^2) := by
  obtain ⟨C,hC,h⟩ := finite_max_central_remainder hne f hU hw hf hrep (w-star)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [h] with t ht
  have ho : RadialCertificate.outwardPoint star w t=w+t • (w-star) := by
    unfold RadialCertificate.outwardPoint RadialCertificate.inwardPoint
    module
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t)]
  simpa only [RadialCertificate.centralDifference,ho,RadialCertificate.inwardPoint] using ht


theorem mem_activeRadialSet_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ) (w r : Vec n) (i : ι) :
    i ∈ activeRadialSet hne f w r ↔ f i w=Finset.univ.sup' hne (fun j => f j w) := by
  simp [activeRadialSet,activeIndices,maximum]

theorem activeRadialJump_zero_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) (f : ι → Vec n → ℝ) (w r : Vec n) :
    activeRadialJump hne f w r=0 ↔
      ∀ i ∈ activeRadialSet hne f w r, ∀ j ∈ activeRadialSet hne f w r,
        (fderiv ℝ (f i) w) r=(fderiv ℝ (f j) w) r := by
  let A := activeRadialSet hne f w r
  let d := fun i => (fderiv ℝ (f i) w) r
  have hA := activeRadialSet_nonempty hne f w r
  constructor
  · intro he i hi j hj
    have hli := Finset.inf'_le d hi
    have hui := Finset.le_sup' d hi
    have hlj := Finset.inf'_le d hj
    have huj := Finset.le_sup' d hj
    change A.sup' hA d-A.inf' hA d=0 at he
    change d i=d j
    linarith
  · intro he
    obtain ⟨i,hi,his⟩ := Finset.exists_mem_eq_sup' hA d
    obtain ⟨j,hj,hji⟩ := Finset.exists_mem_eq_inf' hA d
    change A.sup' hA d-A.inf' hA d=0
    rw [his,hji]
    exact sub_eq_zero.mpr (he i hi j hj)


theorem not_isBigO_of_linear_abs_remainder {D : ℝ → ℝ} {J : ℝ} (hJ : 0 < J)
    (hrem : (fun t => D t-J*abs t) =O[𝓝 0] (fun t : ℝ => t^2)) :
    ¬ D =O[𝓝 0] (fun t : ℝ => t^2) := by
  intro hD
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp hrem
  obtain ⟨M,hM⟩ := Asymptotics.isBigO_iff.mp hD
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hden : 0 < |C|+|M|+1 := by positivity
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < J/(|C|+|M|+1) :=
    (eventually_lt_nhds (div_pos hJ hden)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,ht,hs,hct,hmt⟩ := (hp.and (hsmall.and
    ((hC.filter_mono nhdsWithin_le_nhds).and (hM.filter_mono nhdsWithin_le_nhds)))).exists
  simp only [Real.norm_eq_abs,abs_of_pos ht,abs_of_nonneg (sq_nonneg t)] at hct hmt
  have hb := (lt_div_iff₀ hden).mp hs
  have hcm := mul_le_mul_of_nonneg_right (add_le_add (le_abs_self C) (le_abs_self M)) ht.le
  have hlin : (C+M)*t < J := by nlinarith
  have hmul := mul_lt_mul_of_pos_right hlin ht
  have hc := (abs_le.mp hct).1
  have hm := (abs_le.mp hmt).2
  nlinarith

theorem finite_max_central_not_isBigO {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ} (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {w star : Vec n} (hw : w ∈ U)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ z ∈ U, F z=Finset.univ.sup' hne (fun i => f i z))
    (hJ : 0 < activeRadialJump hne f w (w-star)) :
    ¬ RadialCertificate.centralDifference F star w =O[𝓝 0] (fun t : ℝ => t^2) :=
  not_isBigO_of_linear_abs_remainder hJ (finite_max_central_isBigO (star := star) hne f hU hw hf hrep)

/-- Exact pointwise quadratic-central-difference criterion. This equivalence
is not an assertion that positive-band RS tests every optimal tie. -/
theorem finite_max_central_quadratic_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty) {F : Vec n → ℝ} (f : ι → Vec n → ℝ)
    {U : Set (Vec n)} (hU : IsOpen U) {w star : Vec n} (hw : w ∈ U)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (hrep : ∀ z ∈ U, F z=Finset.univ.sup' hne (fun i => f i z)) :
    RadialCertificate.centralDifference F star w =O[𝓝 0] (fun t : ℝ => t^2) ↔
      ∀ i, f i w=F w → ∀ j, f j w=F w →
        (fderiv ℝ (f i) w) (w-star)=(fderiv ℝ (f j) w) (w-star) := by
  have hmem (i : ι) : i ∈ activeRadialSet hne f w (w-star) ↔ f i w=F w := by
    rw [mem_activeRadialSet_iff,← hrep w hw]
  constructor
  · intro ho
    have hJ : activeRadialJump hne f w (w-star)=0 := by
      by_contra hneJ
      have hp : 0 < activeRadialJump hne f w (w-star) :=
        lt_of_le_of_ne (activeRadialJump_nonneg hne f w (w-star)) (Ne.symm hneJ)
      exact finite_max_central_not_isBigO hne f hU hw hf hrep hp ho
    intro i hi j hj
    exact (activeRadialJump_zero_iff hne f w (w-star)).mp hJ i ((hmem i).mpr hi) j ((hmem j).mpr hj)
  · intro he
    have hJ : activeRadialJump hne f w (w-star)=0 := by
      apply (activeRadialJump_zero_iff hne f w (w-star)).mpr
      intro i hi j hj
      exact he i ((hmem i).mp hi) j ((hmem j).mp hj)
    simpa only [hJ,zero_mul,sub_zero] using finite_max_central_isBigO (star := star) hne f hU hw hf hrep

end BfgsVerification.FiniteMaxRadial




