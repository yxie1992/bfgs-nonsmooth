import BfgsVerification.RateChartData
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
open scoped BigOperators Topology ContDiff NNReal Manifold
open Matrix Filter Set Metric
namespace BfgsVerification.ConstantRankFields
open AffineCriticalObjective ConvexSubdifferential CenteredSmoothSublinear

/-- A finite, buffered smooth partition whose local fields are the actual rate
charts constructed from the original active families. -/
structure FiniteRatePatch {n m : ℕ} (F : Vec n → ℝ) (f : Fin m → Vec n → ℝ)
    (Q : Set (Vec n)) where
  size : ℕ
  center : Fin size → Vec n
  chart : ∀i,RateChart F f (center i)
  cutoff : SmoothPartitionOfUnity (Fin size) 𝓘(ℝ,Vec n) (Vec n) Q
  subordinate : cutoff.IsSubordinate (fun i => ball (center i) ((chart i).radius/4))

theorem exists_finite_ratePatch {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {K : Set (Vec n)} (hK : IsCompact K)
    (hc : ∀p∈K,Nonempty (RateChart F f p)) :
    ∃V Q : Set (Vec n),IsOpen V ∧ K⊆V ∧ closure V⊆Q ∧ IsCompact Q ∧
      Nonempty (FiniteRatePatch F f Q) := by
  classical
  let c (p : K) := Classical.choice (hc p p.property)
  let U (p : K) := ball (p : Vec n) ((c p).radius/4)
  have hU : ∀p,IsOpen (U p) := fun _ => isOpen_ball
  have hcover : K⊆⋃p : K,U p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self (by dsimp [U]; linarith [(c ⟨p,hp⟩).radius_pos])⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU hcover
  let e := (Fintype.equivFin s).symm
  let p (i : Fin (Fintype.card s)) : K := (e i).val
  let N := ⋃i : Fin (Fintype.card s),U (p i)
  have hN : IsOpen N := isOpen_iUnion (fun i => hU (p i))
  have hKN : K⊆N := by
    intro x hx
    obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨e.symm ⟨q,hq⟩,?_⟩
    simpa only [p,Equiv.apply_symm_apply] using hxq
  obtain ⟨r,hr,hrN⟩ := hK.exists_cthickening_subset_open hN hKN
  let Q := cthickening r K
  let V := thickening (r/2) K
  have hQ : IsCompact Q := hK.cthickening
  obtain ⟨χ,hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,Vec n)
    hQ.isClosed (fun i => U (p i)) (fun i => hU (p i)) hrN
  refine ⟨V,Q,isOpen_thickening,self_subset_thickening (by linarith) K,?_,hQ,?_⟩
  · exact (closure_thickening_subset_cthickening (r/2) K).trans
      (cthickening_mono (by linarith : r/2≤r) K)
  · exact ⟨{
      size := Fintype.card s
      center := fun i => p i
      chart := fun i => c (p i)
      cutoff := χ
      subordinate := hχ
    }⟩

def FiniteRatePatch.field {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q) : Vec n → Vec n :=
  fun x => ∑ᶠi,P.cutoff i x • (P.chart i).field x

theorem FiniteRatePatch.fieldC1 {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q) :
    ContDiff ℝ 1 P.field := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  apply P.cutoff.contDiffAt_finsum
  intro i hx
  have hsmall : x∈ball (P.center i) ((P.chart i).radius/4) := P.subordinate i hx
  have hbig : x∈ball (P.center i) (P.chart i).radius :=
    (show dist x (P.center i)<(P.chart i).radius/4 from hsmall).trans_le (by linarith [(P.chart i).radius_pos])
  exact (P.chart i).fieldC1.contDiffAt (isOpen_ball.mem_nhds hbig)

theorem FiniteRatePatch.small_of_cutoff_ne_zero {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q)
    {i : Fin P.size} {x : Vec n} (h : P.cutoff i x≠0) :
    x∈ball (P.center i) ((P.chart i).radius/4) :=
  P.subordinate i (subset_closure h)

theorem FiniteRatePatch.pairing_of_local {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q)
    {x : Vec n} (hx : x∈Q) (g : Vec n)
    (hg : ∀i,P.cutoff i x≠0 → dot g ((P.chart i).field x)=1) :
    dot g (P.field x)=1 := by
  have hs : (∑i,P.cutoff i x)=1 := by
    simpa only [finsum_eq_sum_of_fintype] using P.cutoff.sum_eq_one hx
  rw [field,finsum_eq_sum_of_fintype]
  calc
    dot g (∑i,P.cutoff i x • (P.chart i).field x) =
        ∑i,P.cutoff i x * dot g ((P.chart i).field x) := by
      simp only [dot,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑i,P.cutoff i x := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P.cutoff i x=0
      · simp [hi]
      · rw [hg i hi,mul_one]
    _ = 1 := hs

theorem FiniteRatePatch.supportsPairing {n m : ℕ} {F : Vec n → ℝ}
    {f : Fin m → Vec n → ℝ} {Q : Set (Vec n)} (P : FiniteRatePatch F f Q)
    {x : Vec n} (hx : x∈Q) {g : Vec n} (hg : g∈subdifferential F x) :
    dot g (P.field x)=1 := by
  apply P.pairing_of_local hx g
  intro i hi
  apply (P.chart i).supportsPairing x _ g hg
  exact (show dist x (P.center i)<(P.chart i).radius/4 from P.small_of_cutoff_ne_zero hi).trans_le
    (by linarith [(P.chart i).radius_pos])

end BfgsVerification.ConstantRankFields
