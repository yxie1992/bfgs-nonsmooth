import Mathlib

noncomputable section
open scoped BigOperators
namespace BfgsVerification.RootClusterConservation
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def fiberWeight (s : Finset α) (c : α → β) (w : α → ℕ) (b : β) : ℕ :=
  ∑ a ∈ s.filter (fun a => c a=b), w a

theorem sum_fiberWeight {s : Finset α} {t : Finset β} {c : α → β}
    (hc : ∀a ∈ s, c a ∈ t) (w : α → ℕ) :
    ∑ b ∈ t, fiberWeight s c w b = ∑ a ∈ s, w a :=
  Finset.sum_fiberwise_of_maps_to hc w

theorem fiberWeight_eq_capacity {s : Finset α} {t : Finset β} {c : α → β}
    {w : α → ℕ} {m : β → ℕ} (hc : ∀a ∈ s, c a ∈ t)
    (hle : ∀b ∈ t, fiberWeight s c w b ≤ m b)
    (htotal : ∑a ∈ s, w a = ∑b ∈ t, m b) :
    ∀b ∈ t, fiberWeight s c w b=m b := by
  apply (Finset.sum_eq_sum_iff_of_le hle).mp
  exact (sum_fiberWeight hc w).trans htotal

theorem every_fiber_nonempty {s : Finset α} {t : Finset β} {c : α → β}
    {w : α → ℕ} {m : β → ℕ} (hc : ∀a ∈ s, c a ∈ t)
    (hm : ∀b ∈ t, 0 < m b) (hle : ∀b ∈ t, fiberWeight s c w b ≤ m b)
    (htotal : ∑a ∈ s, w a = ∑b ∈ t, m b) :
    ∀b ∈ t, (s.filter (fun a => c a=b)).Nonempty := by
  intro b hb
  have he := fiberWeight_eq_capacity hc hle htotal b hb
  by_contra hn
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
  have hz : fiberWeight s c w b=0 := by simp only [fiberWeight,hempty,Finset.sum_empty]
  have hp := hm b hb
  omega

theorem every_label_hit {s : Finset α} {t : Finset β} {c : α → β}
    {w : α → ℕ} {m : β → ℕ} (hc : ∀a ∈ s, c a ∈ t)
    (hm : ∀b ∈ t, 0 < m b) (hle : ∀b ∈ t, fiberWeight s c w b ≤ m b)
    (htotal : ∑a ∈ s, w a = ∑b ∈ t, m b) :
    ∀b ∈ t, ∃a ∈ s, c a=b := by
  intro b hb
  obtain ⟨a,ha⟩ := every_fiber_nonempty hc hm hle htotal b hb
  exact ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩

theorem label_bijOn_of_card_eq {s : Finset α} {t : Finset β} {c : α → β}
    {w : α → ℕ} {m : β → ℕ} (hc : ∀a ∈ s, c a ∈ t)
    (hm : ∀b ∈ t, 0 < m b) (hle : ∀b ∈ t, fiberWeight s c w b ≤ m b)
    (htotal : ∑a ∈ s, w a = ∑b ∈ t, m b) (hcard : s.card=t.card) :
    Set.BijOn c (s : Set α) (t : Set β) := by
  let f : s → t := fun a => ⟨c a,hc a a.property⟩
  have hsur : Function.Surjective f := by
    intro b
    obtain ⟨a,ha,hab⟩ := every_label_hit hc hm hle htotal b b.property
    exact ⟨⟨a,ha⟩,Subtype.ext hab⟩
  have hcards : Fintype.card s=Fintype.card t := by simpa only [Fintype.card_coe] using hcard
  have hbij : Function.Bijective f := (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsur,hcards⟩
  refine ⟨hc,?_,?_⟩
  · intro a ha a' ha' he
    exact congrArg Subtype.val (hbij.1 (show f ⟨a,ha⟩=f ⟨a',ha'⟩ from Subtype.ext he))
  · intro b hb
    obtain ⟨a,ha,he⟩ := every_label_hit hc hm hle htotal b hb
    exact ⟨a,ha,he⟩

theorem fiber_singleton_of_card_eq {s : Finset α} {t : Finset β} {c : α → β}
    {w : α → ℕ} {m : β → ℕ} (hc : ∀a ∈ s, c a ∈ t)
    (hm : ∀b ∈ t, 0 < m b) (hle : ∀b ∈ t, fiberWeight s c w b ≤ m b)
    (htotal : ∑a ∈ s, w a = ∑b ∈ t, m b) (hcard : s.card=t.card)
    {a : α} (ha : a ∈ s) : s.filter (fun a' => c a'=c a)={a} := by
  have hinj := (label_bijOn_of_card_eq hc hm hle htotal hcard).injOn
  ext a'
  simp only [Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨ha',he⟩
    exact hinj ha' ha he
  · intro he
    subst a'
    exact ⟨ha,rfl⟩

theorem sole_weight_eq_capacity {s : Finset α} {t : Finset β} {c : α → β}
    {w : α → ℕ} {m : β → ℕ} (hc : ∀a ∈ s, c a ∈ t)
    (hm : ∀b ∈ t, 0 < m b) (hle : ∀b ∈ t, fiberWeight s c w b ≤ m b)
    (htotal : ∑a ∈ s, w a = ∑b ∈ t, m b) (hcard : s.card=t.card)
    {a : α} (ha : a ∈ s) : w a=m (c a) := by
  have he := fiberWeight_eq_capacity hc hle htotal (c a) (hc a ha)
  simpa only [fiberWeight,fiber_singleton_of_card_eq hc hm hle htotal hcard ha,Finset.sum_singleton] using he

theorem fintype_bijective_and_weights [Fintype α] [Fintype β]
    {c : α → β} {w : α → ℕ} {m : β → ℕ}
    (hm : ∀b, 0 < m b)
    (hle : ∀b, fiberWeight Finset.univ c w b ≤ m b)
    (htotal : ∑a, w a = ∑b, m b) (hcard : Fintype.card α=Fintype.card β) :
    Function.Bijective c ∧ ∀a, w a=m (c a) := by
  have hc : ∀a ∈ (Finset.univ : Finset α), c a ∈ (Finset.univ : Finset β) := by simp
  have hm' : ∀b ∈ (Finset.univ : Finset β), 0 < m b := fun b _ => hm b
  have hle' : ∀b ∈ (Finset.univ : Finset β), fiberWeight Finset.univ c w b ≤ m b := fun b _ => hle b
  have hb := label_bijOn_of_card_eq hc hm' hle' htotal (by simpa using hcard)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a a' he
    exact hb.injOn (Finset.mem_univ a) (Finset.mem_univ a') he
  · intro b
    obtain ⟨a,_,he⟩ := every_label_hit hc hm' hle' htotal b (Finset.mem_univ b)
    exact ⟨a,he⟩
  · intro a
    exact sole_weight_eq_capacity hc hm' hle' htotal (by simpa using hcard) (Finset.mem_univ a)

end BfgsVerification.RootClusterConservation
