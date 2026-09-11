import BfgsVerification.FixedNormalProjection

/-! Literal compact-segment and affine-line geometry in Module U.2. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.FixedNormal

/-- A compact convex set with common tangential projection is the image of a
closed scalar interval on the actual fixed normal line. -/
theorem parallel_compact_interval {n : ℕ} {a A : Vec n} {G : Set (Vec n)}
    (hG : IsCompact G) (hGn : G.Nonempty) (hGc : Convex ℝ G)
    (hA : ∀ g ∈ G, tangentProjection a g = A) :
    ∃ l u : ℝ, l ≤ u ∧ G = (fun t : ℝ => A + t • a) '' Icc l u := by
  let D := (fun g => dot a g) '' G
  have hf : (fun g => dot a g) = ⇑(gradientFunctional a).toLinearMap := by
    funext g
    exact (gradientFunctional_apply a g).symm
  have hDc : Convex ℝ D := by
    dsimp only [D]
    rw [hf]
    exact hGc.linear_image (gradientFunctional a).toLinearMap
  have hDn : D.Nonempty := hGn.image _
  have hDk : IsCompact D := hG.image (by
    rw [hf]
    exact (gradientFunctional a).continuous)
  have hDI := eq_Icc_of_connected_compact (hDc.isConnected hDn) hDk
  have hlu : sInf D ≤ sSup D := nonempty_Icc.mp (hDI ▸ hDn)
  refine ⟨sInf D, sSup D, hlu, ?_⟩
  ext g
  constructor
  · intro hg
    refine ⟨dot a g, ?_, ?_⟩
    · rw [← hDI]
      exact ⟨g, hg, rfl⟩
    · exact (sub_eq_iff_eq_add.mp (hA g hg)).symm
  · rintro ⟨t, ht, rfl⟩
    rw [← hDI] at ht
    obtain ⟨g, hg, hgt⟩ := ht
    have he := sub_eq_iff_eq_add.mp (hA g hg)
    change dot a g = t at hgt
    rw [hgt] at he
    change A + t • a ∈ G
    rwa [← he]

/-- Distinct parallel vectors span the complete normal affine line. -/
theorem parallel_affineSpan_eq_range {n : ℕ} {a A : Vec n} {G : Set (Vec n)}
    (hA : ∀ g ∈ G, tangentProjection a g = A)
    {g h : Vec n} (hg : g ∈ G) (hh : h ∈ G) (hne : g ≠ h) :
    (affineSpan ℝ G : Set (Vec n)) = Set.range (fun t : ℝ => A + t • a) := by
  have hge := sub_eq_iff_eq_add.mp (hA g hg)
  have hhe := sub_eq_iff_eq_add.mp (hA h hh)
  have hd : dot a h - dot a g ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    apply hne
    rw [hge, hhe, he]
  ext v
  constructor
  · intro hv
    exact ⟨dot a v, (sub_eq_iff_eq_add.mp (projection_of_mem_affineSpan a A hA hv)).symm⟩
  · rintro ⟨t, rfl⟩
    let c : ℝ := (t - dot a g) / (dot a h - dot a g)
    have hcoef : c * (dot a h - dot a g) + dot a g = t := by
      dsimp [c]
      field_simp [hd]
    have hm := (affineSpan ℝ G).smul_vsub_vadd_mem c
      (subset_affineSpan ℝ G hh) (subset_affineSpan ℝ G hg) (subset_affineSpan ℝ G hg)
    have he : c • (h - g) + g = A + t • a := by
      calc
        _ = c • ((A + dot a h • a) - (A + dot a g • a)) + (A + dot a g • a) := by
          rw [← hge, ← hhe]
        _ = A + (c * (dot a h - dot a g) + dot a g) • a := by module
        _ = A + t • a := by rw [hcoef]
    change c • (h - g) + g ∈ affineSpan ℝ G at hm
    rwa [he] at hm

/-- Source U.2's nontrivial compact interval and full affine-line statement,
with actual subdifferential nonemptiness, compactness and nontriviality derived. -/
theorem nonsmooth_subdifferential_parallel_interval {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x a A : Vec n}
    (hA : ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A)
    (hx : ¬DifferentiableAt ℝ F x) :
    (∃ l u : ℝ, l < u ∧ ConvexSubdifferential.subdifferential F x =
      (fun t : ℝ => A + t • a) '' Icc l u) ∧
    (affineSpan ℝ (ConvexSubdifferential.subdifferential F x) : Set (Vec n)) =
      Set.range (fun t : ℝ => A + t • a) := by
  obtain ⟨g, hg, h, hh, hne⟩ :=
    ConvexSubdifferential.exists_distinct_supports_of_not_differentiableAt hF hx
  obtain ⟨l, u, hlu, he⟩ := parallel_compact_interval
    (ConvexSubdifferential.isCompact_subdifferential hF x)
    (ConvexSubdifferential.subdifferential_nonempty hF x)
    (ConvexSubdifferential.convex_subdifferential F x) hA
  refine ⟨⟨l, u, lt_of_le_of_ne hlu ?_, he⟩, parallel_affineSpan_eq_range hA hg hh hne⟩
  intro hlu'
  rw [hlu', Icc_self, Set.image_singleton] at he
  have hg' : g = A + u • a := by
    have hm : g ∈ ConvexSubdifferential.subdifferential F x := hg
    rwa [he] at hm
  have hh' : h = A + u • a := by
    have hm : h ∈ ConvexSubdifferential.subdifferential F x := hh
    rwa [he] at hm
  exact hne (hg'.trans hh'.symm)

/-- The scalar interval representation is literally the ordinary closed segment. -/
theorem normal_interval_image_eq_segment {n : ℕ} (a A : Vec n) {l u : ℝ}
    (hlu : l ≤ u) :
    (fun t : ℝ => A + t • a) '' Icc l u = segment ℝ (A + l • a) (A + u • a) := by
  let f : ℝ →ᵃ[ℝ] Vec n := AffineMap.lineMap A (A + a)
  have hf (t : ℝ) : f t = A + t • a := by
    simp [f, AffineMap.lineMap_apply_module', add_comm]
  have hfun : (fun t : ℝ => A + t • a) = ⇑f := by funext t; exact (hf t).symm
  rw [hfun, ← segment_eq_Icc hlu, image_segment ℝ f, hf, hf]

/-- Literal nontrivial compact segment parallel to the unit normal, with the
full actual affine-hull identity. -/
theorem nonsmooth_subdifferential_parallel_segment {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {x a A : Vec n} (ha : sqNorm a = 1)
    (hA : ∀ g, Homogeneous.Supports F x g → tangentProjection a g = A)
    (hx : ¬DifferentiableAt ℝ F x) :
    (∃ l u : ℝ, l < u ∧ A + l • a ≠ A + u • a ∧
      ConvexSubdifferential.subdifferential F x = segment ℝ (A + l • a) (A + u • a)) ∧
    (affineSpan ℝ (ConvexSubdifferential.subdifferential F x) : Set (Vec n)) =
      Set.range (fun t : ℝ => A + t • a) := by
  obtain ⟨⟨l, u, hlu, he⟩, hspan⟩ := nonsmooth_subdifferential_parallel_interval hF hA hx
  refine ⟨⟨l, u, hlu, ?_, he.trans (normal_interval_image_eq_segment a A hlu.le)⟩, hspan⟩
  intro hz
  have haa : a ⬝ᵥ a = 1 := by simpa only [dotProduct, sqNorm, pow_two] using ha
  have hd := congrArg (fun v => a ⬝ᵥ v) hz
  simp only [Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul, haa, mul_one] at hd
  linarith

end BfgsVerification.FixedNormal
