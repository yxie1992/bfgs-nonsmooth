import BfgsVerification.UnivariateSignCells
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set Filter
namespace BfgsVerification.RealAlgebraicGeometry

def signSampleRadius (B : Finset ℝ) : ℝ := 1+∑b∈B,|b|

theorem signSampleRadius_pos (B : Finset ℝ) : 0<signSampleRadius B := by
  have hs : 0≤∑b∈B,|b| := Finset.sum_nonneg (fun b _ => abs_nonneg b)
  dsimp [signSampleRadius]
  linarith

theorem mem_lt_signSampleRadius {B : Finset ℝ} {b : ℝ} (hb : b∈B) :
    -signSampleRadius B<b ∧ b<signSampleRadius B := by
  have hh : |b|≤∑r∈B,|r| := Finset.single_le_sum (fun r _ => abs_nonneg r) hb
  dsimp [signSampleRadius]
  constructor <;> linarith [le_abs_self b,neg_abs_le b]

theorem signSampleRadius_not_mem (B : Finset ℝ) :
    -signSampleRadius B∉B ∧ signSampleRadius B∉B := by
  constructor
  · intro h
    exact (lt_irrefl _ (mem_lt_signSampleRadius h).1)
  · intro h
    exact (lt_irrefl _ (mem_lt_signSampleRadius h).2)

theorem signSampleRadius_profiles (B : Finset ℝ) :
    cutProfile B (-signSampleRadius B)=∅ ∧ cutProfile B (signSampleRadius B)=B := by
  classical
  constructor
  · apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro b hb
    obtain ⟨hb,hlt⟩ := Finset.mem_filter.mp hb
    exact (not_lt_of_ge (mem_lt_signSampleRadius hb).1.le) hlt
  · apply Finset.filter_eq_self.mpr
    intro b hb
    exact (mem_lt_signSampleRadius hb).2

/-- A point between two members of an actual finite boundary lies between
its greatest lower boundary and least upper boundary. The whole open gap has
exactly the same cut profile. -/
theorem finite_boundary_gap {B : Finset ℝ} {x : ℝ} (hx : x∉B)
    (hleft : ∃b∈B,b<x) (hright : ∃b∈B,x<b) :
    ∃l u : ℝ,l∈B ∧ u∈B ∧ l<x ∧ x<u ∧
      ∀z∈Ioo l u,z∉B ∧ cutProfile B z=cutProfile B x := by
  classical
  let L := B.filter (fun b => b<x)
  let U := B.filter (fun b => x<b)
  have hL : L.Nonempty := by simpa [L,Finset.filter_nonempty_iff] using hleft
  have hU : U.Nonempty := by simpa [U,Finset.filter_nonempty_iff] using hright
  let l := L.max' hL
  let u := U.min' hU
  have hl : l∈L := Finset.max'_mem _ _
  have hu : u∈U := Finset.min'_mem _ _
  have hlB : l∈B := (Finset.mem_filter.mp hl).1
  have huB : u∈B := (Finset.mem_filter.mp hu).1
  have hlx : l<x := (Finset.mem_filter.mp hl).2
  have hxu : x<u := (Finset.mem_filter.mp hu).2
  have hlow (b : ℝ) (hb : b∈B) (hbx : b<x) : b≤l :=
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hb,hbx⟩)
  have hupp (b : ℝ) (hb : b∈B) (hxb : x<b) : u≤b :=
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb,hxb⟩)
  refine ⟨l,u,hlB,huB,hlx,hxu,?_⟩
  intro z hz
  have hn : z∉B := by
    intro hzb
    rcases lt_or_ge z x with hzx | hxz
    · exact (not_lt_of_ge (hlow z hzb hzx)) hz.1
    · have hxz' : x<z := lt_of_le_of_ne hxz (fun he => hx (he ▸ hzb))
      exact (not_lt_of_ge (hupp z hzb hxz')) hz.2
  refine ⟨hn,?_⟩
  ext b
  simp only [cutProfile,Finset.mem_filter]
  constructor
  · rintro ⟨hb,hbz⟩
    refine ⟨hb,?_⟩
    by_contra hnot
    have hxb : x<b := lt_of_le_of_ne (le_of_not_gt hnot) (fun he => hx (he ▸ hb))
    exact (not_lt_of_ge (hupp b hb hxb)) (hbz.trans hz.2)
  · rintro ⟨hb,hbx⟩
    exact ⟨hb,(hlow b hb hbx).trans_lt hz.1⟩

end BfgsVerification.RealAlgebraicGeometry
