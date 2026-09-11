import BfgsVerification.PlanarSectorContinuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The fixed smooth angular cutoffs used in C are constructed from disjoint
compact normal sectors. Cutoffs are first built on the ambient plane, then
restricted to the Euclidean unit normal; this avoids any angular branch cut. -/
noncomputable section
open scoped BigOperators Topology ContDiff Manifold
open Set Filter Matrix Function
namespace BfgsVerification
namespace PlanarNormalGeometry

/-- A finite family of disjoint closed planar sets admits disjoint open
neighborhoods, each restricted to its independently specified open region. -/
theorem disjoint_open_neighborhoods {m : ℕ} (K U : Fin m → Set (Vec 2))
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hd : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ V : Fin m → Set (Vec 2), (∀ i, IsOpen (V i) ∧ K i ⊆ V i ∧ V i ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) := by
  have hn : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hK i) (hK j) (hd hij)
  obtain ⟨V,hV,hdV⟩ := hn.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))
  refine ⟨fun i => V i ∩ U i,?_,?_⟩
  · intro i
    exact ⟨(hV i).1.inter (hU i),fun w hw => ⟨(hV i).2 hw,hKU i hw⟩,inter_subset_right⟩
  · intro i j hij
    exact (hdV hij).mono inter_subset_left inter_subset_left

/-- Genuine smooth cutoffs with pairwise disjoint supports and a plateau on a
neighborhood of every sector. No cutoff functions are assumed. -/
theorem exists_disjoint_smooth_cutoffs {m : ℕ} (K U : Fin m → Set (Vec 2))
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hd : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ χ : Fin m → Vec 2 → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, ∀ᶠ w in 𝓝ˢ (K i), χ i w=1) ∧
      (∀ i w, χ i w ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, support (χ i) ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))) := by
  obtain ⟨V,hV,hdV⟩ := disjoint_open_neighborhoods K U hK hU hKU hd
  have hex (i : Fin m) := exists_smooth_one_nhds_of_subset_interior
    𝓘(ℝ,Vec 2) (t := V i) (hK i) (by simpa only [(hV i).1.interior_eq] using (hV i).2.1)
  choose χ hχ using hex
  refine ⟨fun i => χ i,?_,?_,?_,?_,?_⟩
  · intro i
    exact (χ i).contMDiff.contDiff
  · intro i
    exact (hχ i).1
  · intro i w
    exact (hχ i).2.2 w
  · intro i w hw
    exact (hV i).2.2 (by by_contra hn; exact hw ((hχ i).2.1 w hn))
  · intro i j hij
    apply (hdV hij).mono
    · intro w hw
      by_contra hn
      exact hw ((hχ i).2.1 w hn)
    · intro w hw
      by_contra hn
      exact hw ((hχ j).2.1 w hn)

/-- Closed supports can also be kept inside the permitted open regions. This
makes positivity uniform under continuous motion of the velocity. -/
theorem exists_disjoint_smooth_tsupport_cutoffs {m : ℕ} (K U : Fin m → Set (Vec 2))
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hd : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ χ : Fin m → Vec 2 → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, ∀ᶠ w in 𝓝ˢ (K i), χ i w=1) ∧
      (∀ i w, χ i w ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, tsupport (χ i) ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  obtain ⟨V,hV,hdV⟩ := disjoint_open_neighborhoods K U hK hU hKU hd
  choose W hW hKW hWV using fun i => normal_exists_closure_subset (hK i) (hV i).1 (hV i).2.1
  have hdW : Pairwise (fun i j => Disjoint (W i) (W j)) := by
    intro i j hij
    exact (hdV hij).mono (subset_closure.trans (hWV i)) (subset_closure.trans (hWV j))
  obtain ⟨χ,hχ,hplateau,hrange,hsupp,_⟩ := exists_disjoint_smooth_cutoffs K W hK hW hKW hd
  have ht (i : Fin m) : tsupport (χ i) ⊆ V i := (closure_mono (hsupp i)).trans (hWV i)
  exact ⟨χ,hχ,hplateau,hrange,fun i => (ht i).trans (hV i).2.2,
    fun i j hij => (hdV hij).mono (ht i) (ht j)⟩

/-- A fixed cutoff plateau covers the entire moving normal sector on a common
level neighborhood, including a neighborhood of each individual normal. -/
theorem normalSector_plateau_motion {a b : ℝ → Vec 2} {t : ℝ} {v : Vec 2}
    (ha : ContinuousAt a t) (hb : ContinuousAt b t)
    (hva : dot (a t) v=1) (hvb : dot (b t) v=1) {χ : Vec 2 → ℝ}
    (hχ : ∀ᶠ w in 𝓝ˢ (normalSector (a t) (b t)), χ w=1) :
    ∀ᶠ s in 𝓝 t, ∀ w ∈ normalSector (a s) (b s), ∀ᶠ z in 𝓝 w, χ z=1 := by
  obtain ⟨U,hU,hKU,hsub⟩ := mem_nhdsSet_iff_exists.mp hχ
  filter_upwards [normalSector_eventually_subset ha hb hva hvb hU hKU] with s hs
  intro w hw
  exact Filter.mem_of_superset (hU.mem_nhds (hs hw)) hsub

/-- Positivity on a compact set persists with one positive lower bound under
continuous motion of the comparison velocity. -/
theorem compact_pairing_uniform_motion {K : Set (Vec 2)} (hK : IsCompact K)
    {v : ℝ → Vec 2} {t : ℝ} (hv : ContinuousAt v t)
    (hpos : ∀ w ∈ K, 0 < dot w (v t)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ s in 𝓝 t, ∀ w ∈ K, η ≤ dot w (v s) := by
  obtain ⟨η,hη,hbound⟩ := hK.exists_forall_le'
    (by unfold dot; fun_prop : ContinuousOn (fun w : Vec 2 => dot w (v t)) K) hpos
  refine ⟨η/2,half_pos hη,?_⟩
  have he : ∀ᶠ s in 𝓝 t, ∀ w ∈ K, η/2 < dot w (v s) := by
    apply hK.eventually_forall_of_forall_eventually
    intro w hw
    have hc : ContinuousAt (fun z : ℝ × Vec 2 => dot z.2 (v z.1)) (t,w) := by
      have hv' : ContinuousAt (fun z : ℝ × Vec 2 => v z.1) (t,w) := hv.comp continuousAt_fst
      simp only [dot,Fin.sum_univ_two]
      have h0 := (continuous_apply 0).continuousAt.comp hv'
      have h1 := (continuous_apply 1).continuousAt.comp hv'
      exact (((continuous_apply 0).continuousAt.comp continuousAt_snd).mul h0).add
        (((continuous_apply 1).continuousAt.comp continuousAt_snd).mul h1)
    exact hc.eventually (lt_mem_nhds ((half_lt_self hη).trans_le (hbound w hw)))
  exact he.mono (fun s hs w hw => (hs w hw).le)

/-- Specialization to actual corner sectors, where the permitted support
region is the positive common-velocity half-plane. -/
theorem exists_normalSector_cutoffs {m : ℕ} (a b v : Fin m → Vec 2)
    (ha : ∀ i, dot (a i) (v i)=1) (hb : ∀ i, dot (b i) (v i)=1)
    (hd : Pairwise (fun i j => Disjoint (normalSector (a i) (b i)) (normalSector (a j) (b j)))) :
    ∃ χ : Fin m → Vec 2 → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, ∀ᶠ w in 𝓝ˢ (normalSector (a i) (b i)), χ i w=1) ∧
      (∀ i w, χ i w ∈ Icc (0 : ℝ) 1) ∧
      (∀ i w, χ i w ≠ 0 → 0 < dot w (v i)) ∧
      Pairwise (fun i j => Disjoint (support (χ i)) (support (χ j))) := by
  obtain ⟨χ,hχ,hplateau,hrange,hsupp,hdisjoint⟩ := exists_disjoint_smooth_cutoffs
    (fun i => normalSector (a i) (b i)) (fun i => {w | 0 < dot w (v i)})
    (fun i => (normalSector_compact (a i) (b i) (v i) (ha i) (hb i)).isClosed)
    (fun i => isOpen_lt continuous_const (by unfold dot; fun_prop))
    (fun i w hw => normalSector_pairing_pos (ha i) (hb i) hw) hd
  exact ⟨χ,hχ,hplateau,hrange,fun i w hw => hsupp i hw,hdisjoint⟩

/-- The actual fixed cutoffs work for every whole sector on nearby levels and
have a uniform positive velocity pairing on their unit-normal supports. -/
theorem exists_moving_normalSector_cutoffs {m : ℕ} (a b v : Fin m → ℝ → Vec 2) (t : ℝ)
    (ha : ∀ i, ContinuousAt (a i) t) (hb : ∀ i, ContinuousAt (b i) t)
    (hv : ∀ i, ContinuousAt (v i) t)
    (hva : ∀ i, dot (a i t) (v i t)=1) (hvb : ∀ i, dot (b i t) (v i t)=1)
    (hd : Pairwise (fun i j => Disjoint (normalSector (a i t) (b i t)) (normalSector (a j t) (b j t)))) :
    ∃ χ : Fin m → Vec 2 → ℝ, ∃ η : Fin m → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i, 0 < η i) ∧
      (∀ i w, χ i w ∈ Icc (0 : ℝ) 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      ∀ᶠ s in 𝓝 t, ∀ i,
        (∀ w ∈ normalSector (a i s) (b i s), ∀ᶠ z in 𝓝 w, χ i z=1) ∧
        (∀ w, sqNorm w ≤ 1 → χ i w ≠ 0 → η i ≤ dot w (v i s)) := by
  obtain ⟨χ,hχ,hplateau,hrange,hsupp,hdisjoint⟩ := exists_disjoint_smooth_tsupport_cutoffs
    (fun i => normalSector (a i t) (b i t)) (fun i => {w | 0 < dot w (v i t)})
    (fun i => (normalSector_compact (a i t) (b i t) (v i t) (hva i) (hvb i)).isClosed)
    (fun i => isOpen_lt continuous_const (by unfold dot; fun_prop))
    (fun i w hw => normalSector_pairing_pos (hva i) (hvb i) hw) hd
  have hex (i : Fin m) : ∃ η : ℝ, 0 < η ∧ ∀ᶠ s in 𝓝 t,
      ∀ w ∈ (CertificateGeometry.euclideanUnitBall ∩ tsupport (χ i)), η ≤ dot w (v i s) := by
    apply compact_pairing_uniform_motion
      (CertificateGeometry.euclideanUnitBall_compact.inter_right isClosed_closure) (hv i)
    intro w hw
    exact hsupp i hw.2
  choose η hη hbound using hex
  refine ⟨χ,η,hχ,hη,hrange,hdisjoint,?_⟩
  apply eventually_all.mpr
  intro i
  filter_upwards [normalSector_plateau_motion (ha i) (hb i) (hva i) (hvb i) (hplateau i),hbound i]
    with s hs hb
  refine ⟨hs,?_⟩
  intro w hw hne
  exact hb w ⟨hw,subset_closure hne⟩

end PlanarNormalGeometry
end BfgsVerification
