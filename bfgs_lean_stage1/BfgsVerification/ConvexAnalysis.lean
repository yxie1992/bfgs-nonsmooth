import BfgsVerification.ObjectiveDefinitions

/-!
# Finite convex objectives and supporting gradients on compact sets

All differentiability hypotheses below concern only the individual point carrying
its gradient. No continuity of the gradient or smoothness on the compact set is
assumed. The coordinate translate argument also bounds arbitrary supporting
vectors, even at nonsmooth points.
-/

noncomputable section
open scoped BigOperators
open Set

namespace BfgsVerification

/-- A real-valued convex function on the whole finite-dimensional space is continuous. -/
theorem convex_continuous {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) : Continuous F := by
  exact continuous_iff_continuousOn_univ.mpr (hF.continuousOn isOpen_univ)

/-- A Fréchet derivative of a finite convex function is a global supporting vector. -/
theorem convex_supporting_inequality {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) {x g : Vec n}
    (hg : HasFDerivAt F (gradientFunctional g) x) (y : Vec n) :
    dot g (y - x) ≤ F y - F x := by
  have hc : ConvexOn ℝ Set.univ (F ∘ AffineMap.lineMap (k := ℝ) x y) := by
    simpa using hF.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hp : HasDerivAt (AffineMap.lineMap (k := ℝ) x y : ℝ → Vec n) (y - x) 0 := by
    change HasDerivAt (fun t : ℝ => t • (y - x) + x) (y - x) 0
    simpa only [one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x
  have hd : HasDerivAt (F ∘ AffineMap.lineMap (k := ℝ) x y) (dot g (y - x)) 0 := by
    simpa using hg.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hs := hc.le_slope_of_hasDerivAt (by trivial) (by trivial)
    (show (0 : ℝ) < 1 by norm_num) hd
  simpa [slope_def_field] using hs

/-- A finite convex objective has a finite lower bound on any compact set. -/
theorem convex_boundedBelow_on_compact {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ b : ℝ, ∀ x ∈ K, b ≤ F x := by
  obtain ⟨b, hb⟩ := hK.bddBelow_image (convex_continuous hF).continuousOn
  exact ⟨b, fun x hx => hb ⟨x, hx, rfl⟩⟩

/-- On a compact set, all supporting vectors of a finite convex objective have
one positive Euclidean norm bound. This includes subgradients at nonsmooth points. -/
theorem convex_supporting_bound_on_compact {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ G : ℝ, 0 < G ∧ ∀ x ∈ K, ∀ g : Vec n,
      (∀ y, dot g (y - x) ≤ F y - F x) → sqNorm g ≤ G ^ 2 := by
  classical
  let e : Fin n → Vec n := fun i => Pi.single i 1
  let S : Set (Vec n) := ⋃ i : Fin n,
    ((fun x : Vec n => x + e i) '' K ∪ (fun x : Vec n => x - e i) '' K)
  have hS : IsCompact S := by
    apply isCompact_iUnion
    intro i
    exact (hK.image (continuous_id.add continuous_const)).union
      (hK.image (continuous_id.sub continuous_const))
  obtain ⟨m, hm⟩ := convex_boundedBelow_on_compact hF hK
  obtain ⟨M, hM⟩ := hS.bddAbove_image (convex_continuous hF).continuousOn
  refine ⟨Real.sqrt ((n : ℝ) * (M - m) ^ 2 + 1), ?_, ?_⟩
  · apply Real.sqrt_pos.mpr
    positivity
  · intro x hx g hg
    have hbound (i : Fin n) : (g i) ^ 2 ≤ (M - m) ^ 2 := by
      have hplus : F (x + e i) ≤ M := by
        apply hM
        exact ⟨x + e i, Set.mem_iUnion.mpr ⟨i, Or.inl ⟨x, hx, rfl⟩⟩, rfl⟩
      have hminus : F (x - e i) ≤ M := by
        apply hM
        exact ⟨x - e i, Set.mem_iUnion.mpr ⟨i, Or.inr ⟨x, hx, rfl⟩⟩, rfl⟩
      have hp := hg (x + e i)
      have hn := hg (x - e i)
      have hdotp : dot g (x + e i - x) = g i := by
        change dotProduct g (x + e i - x) = g i
        rw [add_sub_cancel_left]
        exact dotProduct_single_one g i
      have hdotn : dot g (x - e i - x) = -g i := by
        change dotProduct g (x - e i - x) = -g i
        rw [show x - e i - x = -(e i) by abel]
        simp only [dotProduct_neg, e, dotProduct_single_one]
      rw [hdotp] at hp
      rw [hdotn] at hn
      apply sq_le_sq' <;> linarith [hm x hx]
    calc
      sqNorm g ≤ ∑ _i : Fin n, (M - m) ^ 2 := Finset.sum_le_sum (fun i _ => hbound i)
      _ = (n : ℝ) * (M - m) ^ 2 := by simp
      _ ≤ (n : ℝ) * (M - m) ^ 2 + 1 := by linarith
      _ = (Real.sqrt ((n : ℝ) * (M - m) ^ 2 + 1)) ^ 2 :=
        (Real.sq_sqrt (by positivity)).symm

/-- Actual gradients at differentiable points of a compact set are uniformly
bounded, with no smoothness assumed at other points of that set. -/
theorem convex_gradient_bound_on_compact {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) {K : Set (Vec n)} (hK : IsCompact K) :
    ∃ G : ℝ, 0 < G ∧ ∀ x ∈ K, ∀ g : Vec n,
      HasFDerivAt F (gradientFunctional g) x → sqNorm g ≤ G ^ 2 := by
  obtain ⟨G, hG, hbound⟩ := convex_supporting_bound_on_compact hF hK
  refine ⟨G, hG, ?_⟩
  intro x hx g hg
  exact hbound x hx g (convex_supporting_inequality hF hg)

end BfgsVerification
