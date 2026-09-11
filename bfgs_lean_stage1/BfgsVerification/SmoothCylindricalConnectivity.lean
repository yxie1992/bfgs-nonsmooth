import BfgsVerification.PiecewiseSmoothConcatenation

noncomputable section
open Set
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def PiecewiseSmoothConnected (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, PiecewiseSmoothPathIn S x y

theorem piecewiseSmoothPathIn_equivalence (S : Set E) :
    Equivalence (fun x y : S => PiecewiseSmoothPathIn S x.val y.val) :=
  ⟨fun x => PiecewiseSmoothPathIn.refl x.property,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem PiecewiseSmoothConnected.convex {S : Set E} (hS : Convex ℝ S) :
    PiecewiseSmoothConnected S := fun _ hx _ hy => PiecewiseSmoothPathIn.segment hS hx hy

theorem PiecewiseSmoothConnected.isPathConnected {S : Set E}
    (hS : PiecewiseSmoothConnected S) (hne : S.Nonempty) : IsPathConnected S := by
  exact isPathConnected_iff.mpr ⟨hne, fun x hx y hy => (hS x hx y hy).joinedIn⟩

theorem PiecewiseSmoothConnected.isPreconnected {S : Set E}
    (hS : PiecewiseSmoothConnected S) : IsPreconnected S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact isPreconnected_empty
  · exact (hS.isPathConnected hne).isConnected.isPreconnected

theorem PiecewiseSmoothConnected.image {S : Set E} (hS : PiecewiseSmoothConnected S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : E → F} (hG : ContDiffOn ℝ ∞ G S) : PiecewiseSmoothConnected (G '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (hS x hx y hy).map hG (fun z hz => ⟨z, hz, rfl⟩)

theorem PiecewiseSmoothConnected.graph {S : Set E} (hS : PiecewiseSmoothConnected S)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f S) :
    PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ z.2 = f z.1} := by
  have h := hS.image (contDiffOn_id.prodMk hf)
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz, he⟩
    exact ⟨z.1, hz, Prod.ext rfl he.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩

theorem PiecewiseSmoothConnected.cylinder_of_section {S : Set E} {T : Set (E × ℝ)}
    (hS : PiecewiseSmoothConnected S) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    (hsection : ∀ x ∈ S, (x, f x) ∈ T)
    (hbase : ∀ z ∈ T, z.1 ∈ S)
    (hvertical : ∀ x ∈ S, Convex ℝ {t : ℝ | (x,t) ∈ T}) :
    PiecewiseSmoothConnected T := by
  intro u hu v hv
  have huS := hbase u hu
  have hvS := hbase v hv
  have hup : PiecewiseSmoothPathIn T u (u.1, f u.1) := by
    have h := PiecewiseSmoothPathIn.segment (hvertical u.1 huS) hu (hsection u.1 huS)
    simpa only [Prod.eta] using h.map (contDiffOn_const.prodMk contDiffOn_id)
      (fun t ht => ht)
  have hvp : PiecewiseSmoothPathIn T (v.1, f v.1) v := by
    have h := PiecewiseSmoothPathIn.segment (hvertical v.1 hvS) (hsection v.1 hvS) hv
    simpa only [Prod.eta] using h.map (contDiffOn_const.prodMk contDiffOn_id)
      (fun t ht => ht)
  have hmid : PiecewiseSmoothPathIn T (u.1, f u.1) (v.1, f v.1) :=
    (hS u.1 huS v.1 hvS).map (contDiffOn_id.prodMk hf) hsection
  exact (hup.trans hmid).trans hvp

theorem PiecewiseSmoothConnected.open_band {S : Set E} (hS : PiecewiseSmoothConnected S)
    {a b : E → ℝ} (ha : ContDiffOn ℝ ∞ a S) (hb : ContDiffOn ℝ ∞ b S)
    (hab : ∀ x ∈ S, a x < b x) :
    PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ a z.1 < z.2 ∧ z.2 < b z.1} := by
  apply hS.cylinder_of_section ((ha.add hb).div_const 2)
  · intro x hx
    exact ⟨hx, by linarith [hab x hx], by linarith [hab x hx]⟩
  · intro z hz
    exact hz.1
  · intro x hx
    simpa only [hx, true_and, mem_setOf_eq] using (convex_Ioo (a x) (b x))

theorem PiecewiseSmoothConnected.upper_band {S : Set E} (hS : PiecewiseSmoothConnected S)
    {a : E → ℝ} (ha : ContDiffOn ℝ ∞ a S) :
    PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ a z.1 < z.2} := by
  apply hS.cylinder_of_section (ha.add contDiffOn_const :
    ContDiffOn ℝ ∞ (fun x => a x + 1) S)
  · intro x hx
    exact ⟨hx, by dsimp; linarith⟩
  · intro z hz
    exact hz.1
  · intro x hx
    simpa only [hx, true_and, mem_setOf_eq] using (convex_Ioi (a x))

theorem PiecewiseSmoothConnected.lower_band {S : Set E} (hS : PiecewiseSmoothConnected S)
    {b : E → ℝ} (hb : ContDiffOn ℝ ∞ b S) :
    PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S ∧ z.2 < b z.1} := by
  apply hS.cylinder_of_section (hb.sub contDiffOn_const :
    ContDiffOn ℝ ∞ (fun x => b x - 1) S)
  · intro x hx
    exact ⟨hx, by dsimp; linarith⟩
  · intro z hz
    exact hz.1
  · intro x hx
    simpa only [hx, true_and, mem_setOf_eq] using (convex_Iio (b x))

theorem PiecewiseSmoothConnected.full_cylinder {S : Set E}
    (hS : PiecewiseSmoothConnected S) :
    PiecewiseSmoothConnected {z : E × ℝ | z.1 ∈ S} := by
  apply hS.cylinder_of_section (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => (0 : ℝ)) S)
  · intro x hx
    exact hx
  · intro z hz
    exact hz
  · intro x hx
    change Convex ℝ {t : ℝ | x ∈ S}
    simpa only [hx, setOf_true] using (convex_univ : Convex ℝ (univ : Set ℝ))

end RealAlgebraicGeometry
end BfgsVerification
