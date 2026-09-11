import BfgsVerification.FiniteMaxGradientBound

noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.FiniteAffineLocal
open ConvexSubdifferential

def AffineGerm {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Prop :=
  ∃ A : Vec n →L[ℝ] ℝ, ∃ c : ℝ, F =ᶠ[𝓝 x] (fun z => A z+c)

def PolyhedralGerm {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Prop :=
  ∃ m : ℕ, ∃ A : Fin m → Vec n →L[ℝ] ℝ, ∃ c : Fin m → ℝ,
    LocalFiniteMax F (fun i z => A i z+c i) x

def BinaryAffineGerm {n : ℕ} (F : Vec n → ℝ) (x : Vec n) : Prop :=
  ∃ A B : Vec n →L[ℝ] ℝ, ∃ c d : ℝ,
    F =ᶠ[𝓝 x] (fun z => max (A z+c) (B z+d))

theorem affine_of_differentiable {n : ℕ} {F : Vec n → ℝ} {x : Vec n}
    (h : PolyhedralGerm F x) (hd : DifferentiableAt ℝ F x) : AffineGerm F x := by
  obtain ⟨m,A,c,hrep⟩ := h
  have hf (i : Fin m) : HasFDerivAt (fun z => A i z+c i) (A i) x :=
    (A i).hasFDerivAt.add_const _
  obtain ⟨i,hi⟩ := activeIndices_nonempty hrep
  have hA (j : Fin m) (hj : j ∈ activeIndices F (fun i z => A i z+c i) x) : A j=A i :=
    (FiniteMaxHessian.active_derivative_eq hrep hd.hasFDerivAt (hf j) hj).trans
      (FiniteMaxHessian.active_derivative_eq hrep hd.hasFDerivAt (hf i) hi).symm
  have hc (j : Fin m) (hj : j ∈ activeIndices F (fun i z => A i z+c i) x) : c j=c i := by
    have hjv := mem_activeIndices.mp hj
    have hiv := mem_activeIndices.mp hi
    rw [hA j hj] at hjv
    linarith
  refine ⟨A i,c i,?_⟩
  filter_upwards [hrep,activeIndices_eventually_subset hd.continuousAt
    (fun j => (hf j).continuousAt) hrep] with z hz hsub
  obtain ⟨j,hj⟩ := hz.1
  have hja := hsub (mem_activeIndices.mpr hj)
  calc F z=A j z+c j := hj.symm
       _=A i z+c i := by rw [hA j hja,hc j hja]

theorem AffineGerm.binary {n : ℕ} {F : Vec n → ℝ} {x : Vec n}
    (h : AffineGerm F x) : BinaryAffineGerm F x := by
  obtain ⟨A,c,he⟩ := h
  exact ⟨A,A,c,c,by simpa only [max_self] using he⟩

theorem polyhedral_of_binary_branches {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {x : Vec n} (hrep : LocalFiniteMax F f x)
    (hb : ∀ i, BinaryAffineGerm (f i) x) : PolyhedralGerm F x := by
  choose A B c d he using hb
  let a : Fin m × Fin 2 → Vec n →L[ℝ] ℝ := fun p => if p.2=0 then A p.1 else B p.1
  let b : Fin m × Fin 2 → ℝ := fun p => if p.2=0 then c p.1 else d p.1
  refine ⟨m*2,fun j => a (finProdFinEquiv.symm j),fun j => b (finProdFinEquiv.symm j),?_⟩
  filter_upwards [hrep,eventually_all.mpr he] with z hz hze
  constructor
  · obtain ⟨i,hi⟩ := hz.1
    change f i z=F z at hi
    rw [hze i] at hi
    by_cases hcmp : A i z+c i ≤ B i z+d i
    · refine ⟨finProdFinEquiv (i,1),?_⟩
      simpa only [Equiv.symm_apply_apply,a,b,show (1 : Fin 2)≠0 from by decide,if_false,
        max_eq_right hcmp] using hi
    · refine ⟨finProdFinEquiv (i,0),?_⟩
      simpa only [Equiv.symm_apply_apply,a,b,if_true,max_eq_left (le_of_not_ge hcmp)] using hi
  · rintro _ ⟨j,rfl⟩
    let p := finProdFinEquiv.symm j
    have hle := hz.2 (mem_range_self p.1)
    rw [hze p.1] at hle
    change a p z+b p ≤ F z
    dsimp [a,b]
    split_ifs
    · exact (le_max_left _ _).trans hle
    · exact (le_max_right _ _).trans hle

end BfgsVerification.FiniteAffineLocal
