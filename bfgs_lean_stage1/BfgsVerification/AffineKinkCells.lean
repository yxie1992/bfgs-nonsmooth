import BfgsVerification.AffineKinkAlgebra

/-! Literal finite sign polyhedra and local BFGS basins for scalar residual penalties. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification.AffineKinks

def cellNormal {n : ℕ} {ι : Type*} (P : ι → Kink n) (σ : ι → Bool) (i : ι) : Vec n :=
  if σ i then -(P i).a else (P i).a

def cellOffset {n : ℕ} {ι : Type*} (P : ι → Kink n) (σ : ι → Bool) (i : ι) : ℝ :=
  if σ i then -(P i).b else (P i).b

def cell {n : ℕ} {ι : Type*} (P : ι → Kink n) (σ : ι → Bool) : Set (Vec n) :=
  {x | ∀ i, dot (cellNormal P σ i) x ≤ cellOffset P σ i}

theorem mem_cell_iff {n : ℕ} {ι : Type*} (P : ι → Kink n) (σ : ι → Bool) (x : Vec n) :
    x ∈ cell P σ ↔ ∀ i, if σ i then 0 ≤ (P i).residual x else (P i).residual x ≤ 0 := by
  constructor <;> intro h i <;> have hi := h i
  all_goals cases hs : σ i <;> simp [cellNormal,cellOffset,hs,Kink.residual,dot,Finset.sum_neg_distrib] at hi ⊢ <;> linarith

theorem cell_closed {n : ℕ} {ι : Type*} (P : ι → Kink n) (σ : ι → Bool) :
    IsClosed (cell P σ) := by
  have he : cell P σ=⋂ i, {x | dot (cellNormal P σ i) x ≤ cellOffset P σ i} := by
    ext x
    simp [cell]
  rw [he]
  apply isClosed_iInter
  intro i
  have hc : Continuous (fun x => dot (cellNormal P σ i) x) := by unfold dot; fun_prop
  exact isClosed_le hc continuous_const

theorem cell_convex {n : ℕ} {ι : Type*} (P : ι → Kink n) (σ : ι → Bool) :
    Convex ℝ (cell P σ) := by
  intro x hx z hz a b ha hb hab i
  have he : dot (cellNormal P σ i) (a • x+b • z)=
      a*dot (cellNormal P σ i) x+b*dot (cellNormal P σ i) z := by
    change (cellNormal P σ i) ⬝ᵥ (a • x+b • z)=_
    rw [dotProduct_add,dotProduct_smul,dotProduct_smul]
    rfl
  rw [he]
  have h := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hz i) hb)
  nlinarith [congrArg (fun t => t*cellOffset P σ i) hab]

/-- The sign cells really are finite affine-inequality polyhedra. -/
theorem cell_eq_polyhedron {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n) (σ : ι → Bool) :
    cell P σ=ConvexCellRadial.polyhedron
      (fun j : Fin (Fintype.card ι) => cellNormal P σ ((Fintype.equivFin ι).symm j))
      (fun j : Fin (Fintype.card ι) => cellOffset P σ ((Fintype.equivFin ι).symm j)) := by
  ext x
  constructor
  · intro hx j
    exact hx _
  · intro hx i
    simpa using hx ((Fintype.equivFin ι) i)

theorem cells_cover {n : ℕ} {ι : Type*} (P : ι → Kink n) (x : Vec n) :
    ∃ σ : ι → Bool, x ∈ cell P σ := by
  classical
  refine ⟨fun i => decide (0 ≤ (P i).residual x),?_⟩
  rw [mem_cell_iff]
  intro i
  by_cases h : 0 ≤ (P i).residual x
  · simp [h]
  · simp [h]
    linarith

def piece {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n) (σ : ι → Bool)
    (x : Vec n) : ℝ := ∑ i, (if σ i then (P i).hi else (P i).lo)*(P i).residual x

theorem penalty_eq_piece {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n) (σ : ι → Bool)
    {x : Vec n} (hx : x ∈ cell P σ) : penalty P x=piece P σ x := by
  apply Finset.sum_congr rfl
  intro i hi
  have hs := (mem_cell_iff P σ x).mp hx i
  cases he : σ i
  · simp only [he,Bool.false_eq_true,ite_false] at hs ⊢
    exact max_eq_left (mul_le_mul_of_nonpos_right (P i).ordered hs)
  · simp only [he,ite_true] at hs ⊢
    exact max_eq_right (mul_le_mul_of_nonneg_right (P i).ordered hs)

theorem piece_contDiff {n : ℕ} {ι : Type*} [Fintype ι] (P : ι → Kink n) (σ : ι → Bool)
    {N : WithTop ℕ∞} : ContDiff ℝ N (piece P σ) := by
  unfold piece Kink.residual dot
  apply ContDiff.sum
  intro i hi
  apply ContDiff.mul contDiff_const
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sum
  intro j hj
  fun_prop

/-- Actual absolute-value, hinge and quantile terms give a local basin under
the source's full-objective convexity and unique-minimizer hypotheses. -/
theorem local_kink_basin {n : ℕ} {ι : Type*} [Fintype ι] {F ψ : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) (P : ι → Kink n) {U : Set (Vec n)} (hU : IsOpen U)
    (hψ : CenteredSmoothSublinear.LocallyC11On U ψ) {star : Vec n} (hs : star ∈ U)
    (hrep : ∀ x ∈ U, F x=ψ x+penalty P x)
    (hmin : ∀ x, F star ≤ F x) (hu : ∀ x, F x=F star → x=star) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F star+δ →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F star)) ∧
      Tendsto R.x atTop (𝓝 star) := by
  classical
  apply ConvexCellRadial.local_cells_basin hF (cell P) (fun _ => U)
    (fun σ x => ψ x+piece P σ x) (cell_closed P) (cell_convex P) (fun _ => hU)
    (fun σ => ConvexCellRadial.locallyC11_add hU hψ
      (ConvexCellRadial.contDiffOn_two_locallyC11 hU (piece_contDiff P σ).contDiffOn))
    hU hs (fun _ _ hx => hx.1) (fun x _ => cells_cover P x) _ hmin hu
  intro σ x hx hcell
  rw [hrep x hx,penalty_eq_piece P σ hcell]

end BfgsVerification.AffineKinks
