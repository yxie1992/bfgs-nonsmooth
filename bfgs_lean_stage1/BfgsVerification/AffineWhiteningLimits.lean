import BfgsVerification.AffineWhiteningGeometry

noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineWhitening
open AffineProjection DeterministicLineSearch
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem point_continuous (A : Mat n) : Continuous (point A) := (matrixCLM A⁻¹).continuous

theorem metric_continuous (A : Mat n) : Continuous (metric A) := by
  change Continuous (fun H : Mat n => A⁻¹*H*(A⁻¹)ᵀ)
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem point_limit {ι : Type*} {l : Filter ι} (A : Mat n) {x : ι → Vec n} {p : Vec n}
    (hx : Tendsto x l (𝓝 p)) : Tendsto (fun i => point A (x i)) l (𝓝 (point A p)) :=
  (point_continuous A).continuousAt.tendsto.comp hx

theorem metric_limit_zero {ι : Type*} {l : Filter ι} (A : Mat n) {H : ι → Mat n}
    (hH : Tendsto H l (𝓝 0)) : Tendsto (fun i => metric A (H i)) l (𝓝 0) := by
  simpa only [metric,compress,Matrix.mul_zero,Matrix.zero_mul] using
    (metric_continuous A).continuousAt.tendsto.comp hH

theorem starts_limit_zero (A : Mat n) {F : Vec n → ℝ}
    (hA : A.det≠0) (R : ℕ → AdmissibleBFGSRun n F)
    (hx : Tendsto (fun m => (R m).x 0) atTop (𝓝 0)) :
    Tendsto (fun m => (run A hA (R m)).x 0) atTop (𝓝 0) := by
  simpa only [point,Matrix.mulVec_zero] using point_limit A hx

theorem run_pairing (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (j k : ℕ) (a : ℝ) :
    dot ((run A hA R).g j) (bfgsStep ((run A hA R).H k) ((run A hA R).g k) a)=
      dot (R.g j) (bfgsStep (R.H k) (R.g k) a) := by
  rw [run_g,run_g,run_H,step_equiv A hA,dot_gradient_point A hA]

theorem strict_accept_equiv (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : AdmissibleBFGSRun n F) (k : ℕ) :
    (objective A F ((run A hA R).x (k+1))<objective A F ((run A hA R).x k)+
        R.c₁*dot ((run A hA R).g k)
          (bfgsStep ((run A hA R).H k) ((run A hA R).g k) ((run A hA R).α k)) ∧
      R.c₂*dot ((run A hA R).g k)
          (bfgsStep ((run A hA R).H k) ((run A hA R).g k) ((run A hA R).α k))<
        dot ((run A hA R).g (k+1))
          (bfgsStep ((run A hA R).H k) ((run A hA R).g k) ((run A hA R).α k))) ↔
    (F (R.x (k+1))<F (R.x k)+R.c₁*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k)) ∧
      R.c₂*dot (R.g k) (bfgsStep (R.H k) (R.g k) (R.α k))<
        dot (R.g (k+1)) (bfgsStep (R.H k) (R.g k) (R.α k))) := by
  simp only [run_value,run_alpha,run_pairing]

theorem queries_limit {ι : Type*} {l : Filter ι} (A : Mat n) (hA : A.det≠0)
    (x g : ι → Vec n) (H : ι → Mat n) (a : ι → ℝ) (p : Vec n)
    (hq : Tendsto (fun i => x i+a i • bfgsStep (H i) (g i) 1) l (𝓝 p)) :
    Tendsto (fun i => point A (x i)+a i • bfgsStep (metric A (H i)) (gradient A (g i)) 1)
      l (𝓝 (point A p)) := by
  simp_rw [query_equiv A hA]
  exact point_limit A hq

/-- Uniform locality of a family of complete query sets is preserved by the
same one fixed coordinate change, with no iteration-dependent neighborhood. -/
theorem uniform_locality (A : Mat n) (hA : A.det≠0) {F : Vec n → ℝ}
    (R : ℕ → AdmissibleBFGSRun n F) {ι : Type*} (length : ι → ℝ) (allowed : ℕ → ι → Prop)
    (hR : ∀U : Set (Vec n),U∈𝓝 (0 : Vec n) → ∃N : ℕ,∀m≥N,∀k,
      (R m).x k∈U ∧ ∀q,allowed k q →
        (R m).x k+length q • bfgsStep ((R m).H k) ((R m).g k) 1∈U)
    (U : Set (Vec n)) (hU : U∈𝓝 (0 : Vec n)) :
    ∃N : ℕ,∀m≥N,∀k,(run A hA (R m)).x k∈U ∧ ∀q,allowed k q →
      (run A hA (R m)).x k+length q •
        bfgsStep ((run A hA (R m)).H k) ((run A hA (R m)).g k) 1∈U := by
  have hV : point A ⁻¹' U∈𝓝 (0 : Vec n) := by
    apply (point_continuous A).continuousAt.preimage_mem_nhds
    simpa only [point,Matrix.mulVec_zero] using hU
  obtain ⟨N,hN⟩ := hR (point A ⁻¹' U) hV
  refine ⟨N,?_⟩
  intro m hm k
  obtain ⟨hp,hq⟩ := hN m hm k
  refine ⟨hp,?_⟩
  intro q hq'
  change point A ((R m).x k)+length q • bfgsStep (metric A ((R m).H k)) (gradient A ((R m).g k)) 1∈U
  rw [query_equiv A hA]
  exact hq q hq'

end BfgsVerification.AffineWhitening
