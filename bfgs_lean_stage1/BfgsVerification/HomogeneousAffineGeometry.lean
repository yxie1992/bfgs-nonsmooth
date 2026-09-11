import BfgsVerification.HomogeneousMaxLinear

/-! Finite recurrence and affine separation needed for Module H.B.
All separating vectors and recurrent sets are proved from the stated geometry. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification.Homogeneous

/-- Values appearing infinitely often in a sequence. -/
def recurrentValues {α : Type*} (g : ℕ → α) : Set α :=
  {v | ∃ᶠ k in atTop, g k = v}

theorem recurrentValues_subset_range {α : Type*} (g : ℕ → α) :
    recurrentValues g ⊆ Set.range g := by
  intro v hv
  obtain ⟨k, hk⟩ := hv.exists
  exact ⟨k, hk⟩

/-- A finite-range sequence eventually visits only recurrent values. -/
theorem eventually_mem_recurrentValues {α : Type*} (g : ℕ → α)
    (hfinite : (Set.range g).Finite) : ∀ᶠ k in atTop, g k ∈ recurrentValues g := by
  classical
  have hall : ∀ᶠ k in atTop, ∀ v ∈ Set.range g, g k = v → v ∈ recurrentValues g := by
    apply hfinite.eventually_all.mpr
    intro v _
    by_cases hv : v ∈ recurrentValues g
    · exact Eventually.of_forall (fun _ _ => hv)
    · have hnot : ∀ᶠ k in atTop, g k ≠ v := not_frequently.mp hv
      filter_upwards [hnot] with k hk
      exact fun he => False.elim (hk he)
  filter_upwards [hall] with k hk
  exact hk (g k) ⟨k, rfl⟩ rfl

theorem recurrentValues_nonempty {α : Type*} (g : ℕ → α)
    (hfinite : (Set.range g).Finite) : (recurrentValues g).Nonempty := by
  obtain ⟨k, hk⟩ := (eventually_mem_recurrentValues g hfinite).exists
  exact ⟨g k, hk⟩

theorem recurrentValues_finite {α : Type*} (g : ℕ → α)
    (hfinite : (Set.range g).Finite) : (recurrentValues g).Finite :=
  hfinite.subset (recurrentValues_subset_range g)

/-- Every linear functional on these actual coordinates is an actual dot product. -/
theorem linearFunctional_eq_dot {n : ℕ} (f : Vec n →ₗ[ℝ] ℝ) (g : Vec n) :
    f g = dot (fun i => f (Pi.single i 1)) g := by
  classical
  have hsum : g = ∑ i, g i • (Pi.single i 1 : Vec n) := by
    ext j
    simp [Pi.single_apply]
  rw [hsum, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← hsum]
  unfold dot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- If an affine hull omits zero, an actual vector has dot product one with
every member. No finite-set or topological separation hypothesis is needed. -/
theorem common_component_of_zero_not_mem_affineSpan {n : ℕ} {S : Set (Vec n)}
    (hS : S.Nonempty) (hzero : (0 : Vec n) ∉ affineSpan ℝ S) :
    ∃ v : Vec n, ∀ g ∈ S, dot v g = 1 := by
  classical
  obtain ⟨g₀, hg₀⟩ := hS
  let Q := affineSpan ℝ S
  have hg₀Q : g₀ ∈ Q := subset_affineSpan ℝ S hg₀
  have hnot : g₀ ∉ Q.direction := by
    intro h
    have hz := Q.vadd_mem_of_mem_direction (Q.direction.neg_mem h) hg₀Q
    apply hzero
    simpa only [vadd_eq_add, neg_add_cancel] using hz
  obtain ⟨f, hf, hmap⟩ := Q.direction.exists_dual_map_eq_bot_of_nmem hnot inferInstance
  have hkill : ∀ z ∈ Q.direction, f z = 0 := by
    intro z hz
    have hmem : f z ∈ Q.direction.map f := ⟨z, hz, rfl⟩
    rw [hmap] at hmem
    exact hmem
  let v : Vec n := fun i => f (Pi.single i 1) / f g₀
  refine ⟨v, ?_⟩
  intro g hg
  have hdiff := hkill (g - g₀) (Q.vsub_mem_direction (subset_affineSpan ℝ S hg) hg₀Q)
  rw [map_sub] at hdiff
  have hfg : f g = f g₀ := by linarith
  calc
    dot v g = (dot (fun i => f (Pi.single i 1)) g) / f g₀ := by
      dsimp only [dot, v]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = f g / f g₀ := by rw [← linearFunctional_eq_dot]
    _ = 1 := by rw [hfg, div_self hf]

/-- A finite alphabet has one positive Euclidean gradient bound. -/
theorem finite_range_sqNorm_bound {n : ℕ} (g : ℕ → Vec n)
    (hfinite : (Set.range g).Finite) : ∃ G : ℝ, 0 < G ∧ ∀ k, sqNorm (g k) ≤ G ^ 2 := by
  obtain ⟨B, hB⟩ := (hfinite.image sqNorm).bddAbove
  refine ⟨Real.sqrt (|B| + 1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro k
  rw [Real.sq_sqrt (by positivity)]
  exact (hB ⟨g k, ⟨k, rfl⟩, rfl⟩).trans (by linarith [le_abs_self B])

end BfgsVerification.Homogeneous
