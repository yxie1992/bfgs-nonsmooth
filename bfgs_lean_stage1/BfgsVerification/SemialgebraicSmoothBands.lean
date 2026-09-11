import BfgsVerification.SemialgebraicSmoothConnectivity

noncomputable section
open Set
open scoped Topology ContDiff
namespace BfgsVerification
namespace RealAlgebraicGeometry
variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
@[simp] theorem option_coordinate_eta (v : Option σ → ℝ) :
    (fun j => Option.elim j (v none) (fun i => v (some i))) = v := by
  funext j
  cases j <;> rfl

theorem SemialgebraicPiecewiseSmoothConnected.cylinder_of_section
    {S : Set (σ → ℝ)} {T : Set (Option σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) (hSsa : IsSemialgebraic S)
    {f : (σ → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f S)
    (hfsa : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = f (fun i => v (some i))})
    (hsection : ∀ x ∈ S, (fun j => Option.elim j (f x) x) ∈ T)
    (hbase : ∀ z ∈ T, (fun i => z (some i)) ∈ S)
    (hvertical : ∀ x ∈ S, Convex ℝ {t : ℝ | (fun j => Option.elim j t x) ∈ T}) :
    SemialgebraicPiecewiseSmoothConnected T := by
  intro u hu v hv
  have huS := hbase u hu
  have hvS := hbase v hv
  let L : (σ → ℝ) → Option σ → ℝ := fun x j => Option.elim j (f x) x
  have hup : SemialgebraicPiecewiseSmoothPathIn T u (L (fun i => u (some i))) := by
    have h := semialgebraic_vertical_path (fun i => u (some i)) (hvertical _ huS)
      (show (fun j => Option.elim j (u none) (fun i => u (some i))) ∈ T from by simpa using hu)
      (hsection _ huS)
    simpa only [option_coordinate_eta] using h
  have hvp : SemialgebraicPiecewiseSmoothPathIn T (L (fun i => v (some i))) v := by
    have h := semialgebraic_vertical_path (fun i => v (some i)) (hvertical _ hvS)
      (hsection _ hvS)
      (show (fun j => Option.elim j (v none) (fun i => v (some i))) ∈ T from by simpa using hv)
    simpa only [option_coordinate_eta] using h
  have hmid : SemialgebraicPiecewiseSmoothPathIn T
      (L (fun i => u (some i))) (L (fun i => v (some i))) :=
    (hS _ huS _ hvS).map (option_graph_lift_contDiffOn hf)
      (IsSemialgebraicMapOn.graph_lift hSsa hfsa) hsection
  exact (hup.trans hmid).trans hvp

theorem SemialgebraicPiecewiseSmoothConnected.open_band {S : Set (σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) (hSsa : IsSemialgebraic S)
    {a b : (σ → ℝ) → ℝ} (ha : ContDiffOn ℝ ∞ a S) (hb : ContDiffOn ℝ ∞ b S)
    (hasa : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = a (fun i => v (some i))})
    (hbsa : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = b (fun i => v (some i))})
    (hab : ∀ x ∈ S, a x < b x) :
    SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ a (fun i => v (some i)) < v none ∧
        v none < b (fun i => v (some i))} := by
  have hmid : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = (a (fun i => v (some i)) + b (fun i => v (some i)))/2} := by
    have he : ∀ x, (1/2 : ℝ)*a x + (1/2 : ℝ)*b x+0 = (a x+b x)/2 := by intro x; ring
    simpa only [he] using semialgebraic_scalar_graph_affine hasa hbsa (1/2) (1/2) 0
  apply hS.cylinder_of_section hSsa ((ha.add hb).div_const 2) hmid
  · intro x hx
    exact ⟨hx, by dsimp; linarith [hab x hx], by dsimp; linarith [hab x hx]⟩
  · exact fun _ hz => hz.1
  · intro x hx
    change Convex ℝ {t : ℝ | x ∈ S ∧ a x < t ∧ t < b x}
    simpa only [hx, true_and, mem_setOf_eq] using (convex_Ioo (𝕜 := ℝ) (a x) (b x))

theorem SemialgebraicPiecewiseSmoothConnected.upper_band {S : Set (σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) (hSsa : IsSemialgebraic S)
    {a : (σ → ℝ) → ℝ} (ha : ContDiffOn ℝ ∞ a S)
    (hasa : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = a (fun i => v (some i))}) :
    SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ a (fun i => v (some i)) < v none} := by
  have hplus : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = a (fun i => v (some i))+1} := by
    simpa only [one_mul, zero_mul, add_zero] using semialgebraic_scalar_graph_affine hasa hasa 1 0 1
  apply hS.cylinder_of_section hSsa (ha.add contDiffOn_const) hplus
  · intro x hx
    exact ⟨hx, by dsimp; linarith⟩
  · exact fun _ hz => hz.1
  · intro x hx
    change Convex ℝ {t : ℝ | x ∈ S ∧ a x < t}
    simpa only [hx, true_and, mem_setOf_eq] using (convex_Ioi (𝕜 := ℝ) (a x))

theorem SemialgebraicPiecewiseSmoothConnected.lower_band {S : Set (σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) (hSsa : IsSemialgebraic S)
    {b : (σ → ℝ) → ℝ} (hb : ContDiffOn ℝ ∞ b S)
    (hbsa : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = b (fun i => v (some i))}) :
    SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none < b (fun i => v (some i))} := by
  have hminus : IsSemialgebraic {v : Option σ → ℝ |
      (fun i => v (some i)) ∈ S ∧ v none = b (fun i => v (some i))-1} := by
    simpa only [one_mul, zero_mul, add_zero, sub_eq_add_neg] using
      semialgebraic_scalar_graph_affine hbsa hbsa 1 0 (-1)
  apply hS.cylinder_of_section hSsa (hb.sub contDiffOn_const) hminus
  · intro x hx
    exact ⟨hx, by dsimp; linarith⟩
  · exact fun _ hz => hz.1
  · intro x hx
    change Convex ℝ {t : ℝ | x ∈ S ∧ t < b x}
    simpa only [hx, true_and, mem_setOf_eq] using (convex_Iio (𝕜 := ℝ) (b x))

theorem SemialgebraicPiecewiseSmoothConnected.full_cylinder {S : Set (σ → ℝ)}
    (hS : SemialgebraicPiecewiseSmoothConnected S) (hSsa : IsSemialgebraic S) :
    SemialgebraicPiecewiseSmoothConnected {v : Option σ → ℝ | (fun i => v (some i)) ∈ S} := by
  apply hS.cylinder_of_section hSsa (f := fun _ => 0) contDiffOn_const
    (semialgebraic_scalar_graph_const hSsa 0)
  · exact fun _ hx => hx
  · exact fun _ hx => hx
  · intro x hx
    change Convex ℝ {t : ℝ | x ∈ S}
    simpa only [hx, setOf_true] using (convex_univ : Convex ℝ (univ : Set ℝ))

end RealAlgebraicGeometry
end BfgsVerification
