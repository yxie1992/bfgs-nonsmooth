import BfgsVerification.AffineGapLowerSemicont

/-! Attained positive affine-distance minima on compact noncritical bands.
Lower semicontinuity is used only where actual rank persistence has been proved. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Matrix Filter Set
namespace BfgsVerification
namespace AffineDistance
open AffineBarycentric AffineCriticalObjective ConvexSubdifferential

/-- The epigraph over a compact domain gives an attained minimum for a
nonnegative lower semicontinuous function. -/
theorem compact_nonnegative_lowerSemicontinuous_minimum {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) (f : X → ℝ)
    (hn : ∀ x∈K, 0≤f x) (hl : ∀ x∈K, LowerSemicontinuousAt f x) :
    ∃ x∈K, ∀ y∈K, f x≤f y := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨x0,hx0⟩ := hne
  let z0 : K := ⟨x0,hx0⟩
  let g : K → ℝ := fun x => f x
  have hg : LowerSemicontinuous g := by
    intro x a ha
    exact continuous_subtype_val.continuousAt.tendsto.eventually (hl x x.property a ha)
  let T : Set (K × ℝ) := (univ ×ˢ Icc 0 (g z0)) ∩ {p | g p.1≤p.2}
  have hclosed : IsClosed {p : K × ℝ | g p.1≤p.2} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p hp
    have hlt : p.2<g p.1 := lt_of_not_ge hp
    obtain ⟨a,ha1,ha2⟩ := exists_between hlt
    have h1 : ∀ᶠ q : K × ℝ in 𝓝 p, a<g q.1 :=
      continuous_fst.continuousAt.tendsto.eventually (hg p.1 a ha2)
    have h2 : ∀ᶠ q : K × ℝ in 𝓝 p, q.2<a :=
      continuous_snd.continuousAt.tendsto.eventually (gt_mem_nhds ha1)
    filter_upwards [h1,h2] with q hq1 hq2
    exact (hq2.trans hq1).not_le
  have hT : IsCompact T :=
    (isCompact_univ.prod isCompact_Icc).inter_right hclosed
  have hTne : T.Nonempty := ⟨(z0,g z0),⟨⟨mem_univ _,hn x0 hx0,le_rfl⟩,by change g z0≤g z0; exact le_rfl⟩⟩
  obtain ⟨p,hp,hmin⟩ := hT.exists_isMinOn hTne continuous_snd.continuousOn
  refine ⟨p.1,p.1.property,?_⟩
  intro y hy
  by_cases hle : f y≤g z0
  · have hmem : ((⟨y,hy⟩ : K),f y)∈T := ⟨⟨mem_univ _,hn y hy,hle⟩,by change f y≤f y; exact le_rfl⟩
    exact hp.2.trans (hmin hmem)
  · exact hp.2.trans (hp.1.2.2.trans (le_of_not_ge hle))

theorem objectiveDistance_nonnegative {n : ℕ} (F : Vec n → ℝ) (x : Vec n) :
    0≤objectiveDistance F x := Metric.infDist_nonneg

theorem objectiveDistance_pos_iff {n : ℕ} {F : Vec n → ℝ} (hF : ConvexOn ℝ univ F) (x : Vec n) :
    0<objectiveDistance F x ↔ ¬IsAffineCritical F x := by
  rw [objectiveDistance, affine_distance_eq_norm hF x, norm_pos_iff]
  exact not_congr (canonicalVector_zero_iff hF x)

theorem compact_positive_objectiveDistance_minimum {n : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {K : Set (Vec n)} (hK : IsCompact K) (hne : K.Nonempty)
    (hl : ∀ x∈K, LowerSemicontinuousAt (objectiveDistance F) x)
    (hn : ∀ x∈K, ¬IsAffineCritical F x) :
    ∃ x∈K, 0<objectiveDistance F x ∧ ∀ y∈K, objectiveDistance F x≤objectiveDistance F y := by
  obtain ⟨x,hx,hmin⟩ := compact_nonnegative_lowerSemicontinuous_minimum hK hne (objectiveDistance F)
    (fun x _ => objectiveDistance_nonnegative F x) hl
  exact ⟨x,hx,(objectiveDistance_pos_iff hF x).mpr (hn x hx),hmin⟩

/-- Every nonempty compact positive band in a locally correct full-rank finite
maximum has an attained strictly positive actual affine-subdifferential gap. -/
theorem finite_max_compact_positive_band {n m : ℕ} {F : Vec n → ℝ}
    (hF : ConvexOn ℝ univ F) {f : Fin m → Vec n → ℝ}
    (g : Vec n → Fin m → Vec n) (star : Vec n) {K : Set (Vec n)}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hrep : ∀ p∈K, LocalFiniteMax F f p)
    (hg : ∀ p∈K, ∀ᶠ q in 𝓝 p, ∀ i, HasFDerivAt (f i) (gradientFunctional (g q i)) q)
    (hc : ∀ p∈K, ∀ i, ContinuousAt (fun q => g q i) p)
    (hind : ∀ p∈K, AffineIndependent ℝ (g p))
    (hcorrect : ∀ p∈K, AffineCorrectAt F p) (hpositive : ∀ p∈K, F star<F p) :
    ∃ p∈K, 0<objectiveDistance F p ∧ ∀ q∈K, objectiveDistance F p≤objectiveDistance F q := by
  apply compact_positive_objectiveDistance_minimum hF hK hne
  · exact fun p hp => objectiveDistance_lowerSemicontinuousAt hF g p
      (hrep p hp) (hg p hp) (hc p hp) (hind p hp)
  · intro p hp hcrit
    have hs := zero_mem_iff_global_minimum.mp (hcorrect p hp hcrit) star
    exact (hpositive p hp).not_le hs

end AffineDistance
end BfgsVerification
