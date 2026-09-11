import BfgsVerification.PolynomialFiberDerivatives

/-! Exact root multiplicity of every nonzero actual fiber is detected by
finitely many polynomial derivative tests. Identically zero fibers remain a
separate algebraic locus. -/
noncomputable section
open Set MvPolynomial
namespace BfgsVerification
namespace RealAlgebraicGeometry

variable {n : ℕ}

theorem eval_derivative_rootMultiplicity_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) :
    (Polynomial.derivative^[p.rootMultiplicity t] p).eval t ≠ 0 := by
  rw [Polynomial.eval_iterate_derivative_rootMultiplicity,nsmul_eq_mul]
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (p.rootMultiplicity t))
    (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero t hp)

theorem rootMultiplicity_eq_iff_derivative_tests {p : Polynomial ℝ} (hp : p ≠ 0)
    (t : ℝ) (m : ℕ) :
    p.rootMultiplicity t = m ↔
      (∀ j ∈ Finset.range m, (Polynomial.derivative^[j] p).eval t = 0) ∧
      (Polynomial.derivative^[m] p).eval t ≠ 0 := by
  constructor
  · intro hm
    constructor
    · intro j hj
      exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
        (hm ▸ Finset.mem_range.mp hj)
    · rw [← hm]
      exact eval_derivative_rootMultiplicity_ne_zero hp t
  · rintro ⟨hzero,hne⟩
    apply le_antisymm
    · by_contra h
      exact hne (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega))
    · by_contra h
      exact eval_derivative_rootMultiplicity_ne_zero hp t
        (hzero _ (Finset.mem_range.mpr (by omega)))

theorem rootMultiplicity_le_natDegree {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) :
    p.rootMultiplicity t ≤ p.natDegree := by
  have h := Polynomial.natDegree_le_of_dvd (p.pow_rootMultiplicity_dvd t) hp
  simpa using h

def multiplicityStratum (p : MvPolynomial (Option (Fin n)) ℝ) (m : ℕ) :
    Set (Option (Fin n) → ℝ) :=
  {v | fiberPolynomial p (fun i => v (some i)) ≠ 0 ∧
    (fiberPolynomial p (fun i => v (some i))).rootMultiplicity (v none) = m}

theorem multiplicityStratum_iff (p : MvPolynomial (Option (Fin n)) ℝ) (m : ℕ)
    (v : Option (Fin n) → ℝ) :
    v ∈ multiplicityStratum p m ↔
      (∀ j ∈ Finset.range m, MvPolynomial.eval v (verticalDerivative p j) = 0) ∧
        MvPolynomial.eval v (verticalDerivative p m) ≠ 0 := by
  simp only [multiplicityStratum,mem_setOf_eq,verticalDerivative_eval]
  constructor
  · rintro ⟨hp,hm⟩
    exact (rootMultiplicity_eq_iff_derivative_tests hp (v none) m).mp hm
  · rintro ⟨hz,hn⟩
    have hp : fiberPolynomial p (fun i => v (some i)) ≠ 0 := by
      intro he
      apply hn
      rw [he]
      simp
    exact ⟨hp,(rootMultiplicity_eq_iff_derivative_tests hp (v none) m).mpr ⟨hz,hn⟩⟩

theorem multiplicityStratum_semialgebraic (p : MvPolynomial (Option (Fin n)) ℝ) (m : ℕ) :
    IsSemialgebraic (multiplicityStratum p m) := by
  have h := (isSemialgebraic_finset_inter (Finset.range m)
    (fun j => {v | MvPolynomial.eval v (verticalDerivative p j) = 0})
    (fun j _ => isSemialgebraic_equal_zero _)).inter
      (isSemialgebraic_equal_zero (verticalDerivative p m)).compl
  convert h using 1
  ext v
  simp only [multiplicityStratum_iff,mem_inter_iff,mem_iInter,mem_setOf_eq,mem_compl_iff]

def zeroFiberCylinder (p : MvPolynomial (Option (Fin n)) ℝ) :
    Set (Option (Fin n) → ℝ) := {v | fiberPolynomial p (fun i => v (some i)) = 0}

theorem zeroFiberCylinder_semialgebraic (p : MvPolynomial (Option (Fin n)) ℝ) :
    IsSemialgebraic (zeroFiberCylinder p) := by
  have h := (fiberPolynomial_zero_semialgebraic p).polynomial_preimage
    (fun i => MvPolynomial.X (some i))
  simpa [zeroFiberCylinder] using h

theorem multiplicityStratum_degree_bound (p : MvPolynomial (Option (Fin n)) ℝ)
    {v : Option (Fin n) → ℝ} {m : ℕ} (hv : v ∈ multiplicityStratum p m) :
    m ≤ p.degreeOf none := by
  have h := (rootMultiplicity_le_natDegree hv.1 (v none)).trans
    (fiberPolynomial_natDegree_le p (fun i => v (some i)))
  rwa [hv.2] at h

theorem multiplicityStrata_disjoint (p : MvPolynomial (Option (Fin n)) ℝ)
    {j k : ℕ} (hjk : j ≠ k) : Disjoint (multiplicityStratum p j) (multiplicityStratum p k) := by
  rw [Set.disjoint_left]
  intro v hj hk
  exact hjk (hj.2.symm.trans hk.2)

theorem zeroFiber_disjoint_multiplicityStratum (p : MvPolynomial (Option (Fin n)) ℝ) (m : ℕ) :
    Disjoint (zeroFiberCylinder p) (multiplicityStratum p m) := by
  rw [Set.disjoint_left]
  exact fun v hz hm => hm.1 hz

theorem multiplicityStrata_partition (p : MvPolynomial (Option (Fin n)) ℝ) :
    zeroFiberCylinder p ∪
      (⋃ m ∈ Finset.range (p.degreeOf none + 1), multiplicityStratum p m) = univ := by
  ext v
  simp only [mem_union,mem_iUnion,mem_univ,iff_true]
  by_cases hz : fiberPolynomial p (fun i => v (some i)) = 0
  · exact Or.inl hz
  · let m := (fiberPolynomial p (fun i => v (some i))).rootMultiplicity (v none)
    have hm : v ∈ multiplicityStratum p m := ⟨hz,rfl⟩
    exact Or.inr ⟨m,Finset.mem_range.mpr (Nat.lt_succ_of_le
      (multiplicityStratum_degree_bound p hm)),hm⟩

theorem multiplicityStratum_root_iff (p : MvPolynomial (Option (Fin n)) ℝ)
    {v : Option (Fin n) → ℝ} {m : ℕ} (hv : v ∈ multiplicityStratum p m) :
    MvPolynomial.eval v p = 0 ↔ 0 < m := by
  have he : MvPolynomial.eval v p =
      (fiberPolynomial p (fun i => v (some i))).eval (v none) := by
    simpa [verticalDerivative] using verticalDerivative_eval p v 0
  rw [he,← hv.2]
  exact (Polynomial.rootMultiplicity_pos hv.1).symm

theorem root_multiplicity_partition (p : MvPolynomial (Option (Fin n)) ℝ) :
    {v | MvPolynomial.eval v p = 0} = zeroFiberCylinder p ∪
      (⋃ m ∈ Finset.Icc 1 (p.degreeOf none), multiplicityStratum p m) := by
  ext v
  simp only [mem_setOf_eq,mem_union,mem_iUnion]
  constructor
  · intro hv
    by_cases hz : fiberPolynomial p (fun i => v (some i)) = 0
    · exact Or.inl hz
    · let m := (fiberPolynomial p (fun i => v (some i))).rootMultiplicity (v none)
      have hm : v ∈ multiplicityStratum p m := ⟨hz,rfl⟩
      exact Or.inr ⟨m,Finset.mem_Icc.mpr ⟨(multiplicityStratum_root_iff p hm).mp hv,
        multiplicityStratum_degree_bound p hm⟩,hm⟩
  · rintro (hz | ⟨m,hm,hv⟩)
    · have he := verticalDerivative_eval p v 0
      change fiberPolynomial p (fun i => v (some i)) = 0 at hz
      rw [hz] at he
      simpa [verticalDerivative] using he
    · exact (multiplicityStratum_root_iff p hv).mpr (Finset.mem_Icc.mp hm).1

end RealAlgebraicGeometry
end BfgsVerification
