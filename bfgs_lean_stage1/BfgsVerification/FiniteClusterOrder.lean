import BfgsVerification.RootClusterBoundsTargets
import Mathlib.Data.Finset.Sort

noncomputable section
open Filter Set Polynomial
open scoped Topology
namespace BfgsVerification
namespace RealAlgebraicGeometry

theorem finite_cluster_assignment (S T : Finset ℝ) (J : ℝ → Set ℝ)
    (hcover : ∀ t ∈ T, ∃ b ∈ S, t ∈ J b)
    (hdisj : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → Disjoint (J b) (J c)) :
    ∃ c : ℝ → ℝ, (∀ t ∈ T, c t ∈ S ∧ t ∈ J (c t)) ∧
      ∀ t ∈ T, ∀ b ∈ S, c t = b ↔ t ∈ J b := by
  classical
  choose f hf hfJ using (fun t : T => hcover t t.2)
  let c : ℝ → ℝ := fun t => if ht : t ∈ T then f ⟨t,ht⟩ else 0
  have hc : ∀ t ∈ T, c t ∈ S ∧ t ∈ J (c t) := by
    intro t ht
    simpa only [c,dif_pos ht] using And.intro (hf ⟨t,ht⟩) (hfJ ⟨t,ht⟩)
  refine ⟨c,hc,?_⟩
  intro t ht b hb
  constructor
  · intro he
    simpa only [he] using (hc t ht).2
  · intro hj
    by_contra he
    exact Set.disjoint_left.mp (hdisj (c t) (hc t ht).1 b hb he) (hc t ht).2 hj

theorem cluster_assignment_strictMonoOn (S T : Finset ℝ) (δ : ℝ) (c : ℝ → ℝ)
    (hc : ∀ t ∈ T, c t ∈ S ∧ t ∈ Icc (c t-δ) (c t+δ))
    (hinj : Set.InjOn c T)
    (hdisj : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' →
      Disjoint (Icc (b-δ) (b+δ)) (Icc (b'-δ) (b'+δ))) :
    StrictMonoOn c T := by
  intro x hx y hy hxy
  have hxc := hc x hx
  have hyc := hc y hy
  have hle : c x ≤ c y := by
    by_contra hn
    have hr : c y < c x := lt_of_not_ge hn
    have hm : x ∈ Icc (c y-δ) (c y+δ) := by
      constructor <;> linarith [hxc.2.1,hxc.2.2,hyc.2.1,hyc.2.2]
    exact Set.disjoint_left.mp (hdisj _ hxc.1 _ hyc.1 hr.ne') hxc.2 hm
  exact lt_of_le_of_ne hle (fun he => hxy.ne (hinj hx hy he))

theorem ordered_cluster_assignment (S T : Finset ℝ) (δ : ℝ) (c : ℝ → ℝ)
    (hcard : T.card = S.card)
    (hc : ∀ t ∈ T, c t ∈ S ∧ t ∈ Icc (c t-δ) (c t+δ))
    (hinj : Set.InjOn c T)
    (hdisj : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' →
      Disjoint (Icc (b-δ) (b+δ)) (Icc (b'-δ) (b'+δ))) :
    ∀ i : Fin S.card, c (T.orderEmbOfFin hcard i) = S.orderEmbOfFin rfl i := by
  have hm := cluster_assignment_strictMonoOn S T δ c hc hinj hdisj
  have he : (fun i : Fin S.card => c (T.orderEmbOfFin hcard i)) = S.orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl
      (fun i => (hc _ (T.orderEmbOfFin_mem hcard i)).1)
      (fun i j hij => hm (T.orderEmbOfFin_mem hcard i) (T.orderEmbOfFin_mem hcard j)
        ((T.orderEmbOfFin hcard).strictMono hij))
  exact fun i => congrFun he i

end RealAlgebraicGeometry
end BfgsVerification
