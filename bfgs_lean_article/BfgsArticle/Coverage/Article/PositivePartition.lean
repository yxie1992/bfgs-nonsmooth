import BfgsVerification.QuadraticCellRadial

/-!
# Lean coverage: `paper/statements/positive_partition.tex`

Theorem `art:polyhedral` ("Local convergence on finite polyhedral cells"), which
`paper/sections/local.tex` inputs at line 46. Its proof (`local.tex:48-76`) and the displays
of that proof are covered in `BfgsArticle.Coverage.Article.Local`. Register:
`editorial/lean_coverage/register/A_positive_partition.json`.

## Standing assumptions (the hypotheses of the theorem, with these names)

* `_hn : 1 ≤ n` is $n\ge1$; `F : Vec n → ℝ` with `hF : ConvexOn ℝ univ F` is a finite convex
  $F:\R^n\to\R$;
* `hmin : ∀ x, F xstar ≤ F x` and `huniq : ∀ x, F x = F xstar → x = xstar` say that `xstar` is
  the unique minimizer $x_*$;
* `hU : IsOpen U`, `hxU : xstar ∈ U`: $U$ is an open neighborhood of $x_*$;
* the cells are indexed by a finite type `ι`; `hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}`
  says that $P_i$ is the polyhedron cut out by the `m i` affine inequalities
  $a_{ij}^Tx\le b_{ij}$ (such a set is automatically closed, `ConvexCellRadial.polyhedron_closed`);
  `_hfull : ∀ i, (interior (P i)).Nonempty` says that it is full-dimensional; and
  `hcover : U ⊆ ⋃ i, P i` that the cells cover $U$;
* `hV : ∀ i, IsOpen (V i)` and `hUV : ∀ i, U ∩ P i ⊆ V i` are the open sets $V_i\supset U\cap P_i$;
  `hf : ∀ i, LocallyC11On (V i) (f i)` is $f_i\in C^{1,1}_{\rm loc}(V_i)$, where the library's
  `CenteredSmoothSublinear.LocallyC11On V f` is
  `DifferentiableOn ℝ f V ∧ LocallyLipschitzOn V (fderiv ℝ f)`;
* `hrep : ∀ i, ∀ x ∈ U ∩ P i, F x = f i x` is display `disp/001`.

An infinite full-BFGS run with arbitrary $H_0\succ0$, differentiable accepted iterates and
fixed Armijo--weak-Wolfe constants $0<c_1<c_2<1$ is an `AdmissibleBFGSRun n F` (Definition
`art:admissible`); its iterates are `R.x k`.

The hypothesis `_hfull` is not needed by the proof: the library theorem
`ConvexCellRadial.finite_polyhedral_basin` allows lower-dimensional cells. An `example` at the
end shows that the standing assumptions can all hold at once.
-/

noncomputable section
open Set Filter Topology BfgsVerification

namespace BfgsCoverage.Article.PositivePartition

/-- Item `A/positive_partition/theorem/art:polyhedral`
(`paper/statements/positive_partition.tex:1-18`), Theorem `art:polyhedral`, including its
displays `A/positive_partition/disp/001` (lines 6-8) and `A/positive_partition/disp/002`
(lines 13-15).

Let $n\ge1$ and let $F:\R^n\to\R$ be finite and convex, with a unique minimizer $x_*$.
Suppose an open neighborhood $U$ of $x_*$ is covered by finitely many closed full-dimensional
polyhedra $P_i$. For each $i$, suppose there is an open set $V_i\supset U\cap P_i$ and a
function $f_i\in C^{1,1}_{\rm loc}(V_i)$ such that $F(x)=f_i(x)$ $(x\in U\cap P_i)$. Then there
exists $\varepsilon>0$ such that every infinite full-BFGS run with arbitrary $H_0\succ0$,
differentiable accepted iterates, fixed Armijo--weak-Wolfe constants $0<c_1<c_2<1$, and
$F(x_0)\le F(x_*)+\varepsilon$ satisfies
\[ x_k\in U\quad(k\ge0),\qquad F(x_k)\to F(x_*),\qquad x_k\to x_*. \]
The basin is chosen before the run and its initial matrix (`∃ ε` precedes `∀ R`). Only the full
objective must be convex; the extensions need not be convex outside their cells (no convexity
hypothesis on the `f i`). -/
theorem polyhedral {n : ℕ} (_hn : 1 ≤ n) (F : Vec n → ℝ) (hF : ConvexOn ℝ univ F)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x) (huniq : ∀ x, F x = F xstar → x = xstar)
    (U : Set (Vec n)) (hU : IsOpen U) (hxU : xstar ∈ U)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ∀ i, Fin (m i) → Vec n) (b : ∀ i, Fin (m i) → ℝ)
    (P : ι → Set (Vec n)) (hP : ∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j})
    (_hfull : ∀ i, (interior (P i)).Nonempty) (hcover : U ⊆ ⋃ i, P i)
    (V : ι → Set (Vec n)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U ∩ P i ⊆ V i)
    (f : ι → Vec n → ℝ) (hf : ∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i))
    (hrep : ∀ i, ∀ x ∈ U ∩ P i, F x = f i x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : AdmissibleBFGSRun n F, F (R.x 0) ≤ F xstar + ε →
      (∀ k, R.x k ∈ U) ∧ Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
        Tendsto R.x atTop (𝓝 xstar) := by
  have hPe : ∀ i, P i = ConvexCellRadial.polyhedron (a i) (b i) := fun i => hP i
  refine ConvexCellRadial.finite_polyhedral_basin hF a b V f hV hf hU hxU
    (fun i => by rw [← hPe i]; exact hUV i) ?_ ?_ hmin huniq
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨i, by rw [← hPe i]; exact hi⟩
  · intro i x hx hxi
    exact hrep i x ⟨hx, by rw [hPe i]; exact hxi⟩

/-! ### Non-vacuity -/

/-- The standing assumptions can all hold at once: $n=1$, $F(x)=|x_1|$, $x_*=0$, $U=\R$, the two
half-lines $P_0=\{x_1\le0\}$ and $P_1=\{-x_1\le0\}$ with $V_i=\R$, $f_0(x)=-x_1$, $f_1(x)=x_1$. -/
example : ∃ (F : Vec 1 → ℝ) (xstar : Vec 1) (U : Set (Vec 1)) (a : Fin 2 → Fin 1 → Vec 1)
    (b : Fin 2 → Fin 1 → ℝ) (P V : Fin 2 → Set (Vec 1)) (f : Fin 2 → Vec 1 → ℝ),
    1 ≤ 1 ∧ ConvexOn ℝ univ F ∧ (∀ x, F xstar ≤ F x) ∧ (∀ x, F x = F xstar → x = xstar) ∧
      IsOpen U ∧ xstar ∈ U ∧ (∀ i, P i = {x | ∀ j, dot (a i j) x ≤ b i j}) ∧
      (∀ i, (interior (P i)).Nonempty) ∧ U ⊆ ⋃ i, P i ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, U ∩ P i ⊆ V i) ∧ (∀ i, CenteredSmoothSublinear.LocallyC11On (V i) (f i)) ∧
      (∀ i, ∀ x ∈ U ∩ P i, F x = f i x) := by
  let s : Fin 2 → ℝ := ![1, -1]
  have hs0 : s 0 = 1 := rfl
  have hs1 : s 1 = -1 := rfl
  have hdot : ∀ (i : Fin 2) (x : Vec 1), dot (fun _ : Fin 1 => s i) x = s i * x 0 := by
    intro i x
    simp [dot]
  refine ⟨fun x => |x 0|, 0, univ, fun i _ => fun _ => s i, fun _ _ => 0,
    fun i => {x | ∀ j : Fin 1, dot ((fun i _ => fun _ => s i : Fin 2 → Fin 1 → Vec 1) i j) x ≤ 0},
    fun _ => univ, fun i x => -(s i * x 0), le_rfl, ?_, ?_, ?_, isOpen_univ, mem_univ _,
    fun i => rfl, ?_, ?_, fun _ => isOpen_univ, fun _ _ _ => mem_univ _, ?_, ?_⟩
  · -- convexity of `|x 0|`
    have hl : ConvexOn ℝ univ (fun x : Vec 1 => x 0) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).toLinearMap.convexOn
        convex_univ
    have hn : ConvexOn ℝ univ (fun x : Vec 1 => -x 0) :=
      (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).toLinearMap.convexOn
        convex_univ
    refine (hl.sup hn).congr ?_
    intro x _
    simp [abs_eq_max_neg]
  · intro x
    simp
  · intro x hx
    ext i
    fin_cases i
    simpa using hx
  · intro i
    have hopen : IsOpen {x : Vec 1 | s i * x 0 < 0} :=
      isOpen_lt (continuous_const.mul (continuous_apply 0)) continuous_const
    refine ⟨fun _ => -s i, ?_⟩
    rw [mem_interior]
    refine ⟨{x : Vec 1 | s i * x 0 < 0}, ?_, hopen, ?_⟩
    · intro x hx j
      simp only [hdot]
      exact (mem_setOf_eq ▸ hx).le
    · show s i * -s i < 0
      fin_cases i <;> norm_num [s]
  · intro x _
    rcases le_or_lt (x 0) 0 with h | h
    · refine mem_iUnion.mpr ⟨0, fun j => ?_⟩
      show dot (fun _ => s 0) x ≤ 0
      rw [hdot, hs0]
      linarith
    · refine mem_iUnion.mpr ⟨1, fun j => ?_⟩
      show dot (fun _ => s 1) x ≤ 0
      rw [hdot, hs1]
      linarith
  · intro i
    apply ConvexCellRadial.contDiffOn_two_locallyC11 isOpen_univ
    exact (contDiff_const.mul (contDiff_apply ℝ ℝ (0 : Fin 1))).neg.contDiffOn
  · intro i x hx
    have h : dot (fun _ => s i) x ≤ 0 := hx.2 0
    rw [hdot] at h
    show |x 0| = -(s i * x 0)
    fin_cases i
    · have h' : x 0 ≤ 0 := by simpa [s] using h
      simp [s, abs_of_nonpos h']
    · have h' : 0 ≤ x 0 := by simp [s] at h; linarith
      simp [s, abs_of_nonneg h']

end BfgsCoverage.Article.PositivePartition
