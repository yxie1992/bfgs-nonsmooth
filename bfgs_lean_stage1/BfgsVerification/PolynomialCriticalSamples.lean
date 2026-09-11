import BfgsVerification.NonzeroFamilyProduct

noncomputable section
open scoped BigOperators
open Set Filter Polynomial
namespace BfgsVerification.RealAlgebraicGeometry

/-- Actual finite critical/root/tail samples for one real polynomial. -/
def polynomialSignSamples (p : Polynomial ℝ) : Finset ℝ := by
  classical
  exact p.roots.toFinset ∪ p.derivative.roots.toFinset ∪
    {-signSampleRadius p.roots.toFinset,signSampleRadius p.roots.toFinset}

theorem derivative_ne_zero_of_real_root {p : Polynomial ℝ} (hp : p≠0)
    {a : ℝ} (ha : p.eval a=0) : p.derivative≠0 := by
  intro hd
  have he := Polynomial.eq_C_of_derivative_eq_zero hd
  have hc : p.coeff 0=0 := by
    have hh := congrArg (fun f : Polynomial ℝ => f.eval a) he
    dsimp only at hh
    rw [ha,Polynomial.eval_C] at hh
    exact hh.symm
  apply hp
  simpa only [hc,Polynomial.C_0] using he

/-- Every point is either a root sample or has the same actual root-cut profile
as a derivative-root sample or one of the two explicit tails. -/
theorem exists_sample_same_or_profile {p : Polynomial ℝ} (hp : p≠0) (x : ℝ) :
    ∃y∈polynomialSignSamples p,y=x ∨
      (x∉p.roots.toFinset ∧ y∉p.roots.toFinset ∧
        cutProfile p.roots.toFinset x=cutProfile p.roots.toFinset y) := by
  classical
  let B := p.roots.toFinset
  by_cases hx : x∈B
  · exact ⟨x,Finset.mem_union_left _ (Finset.mem_union_left _ hx),Or.inl rfl⟩
  by_cases hl : ∃b∈B,b<x
  · by_cases hu : ∃b∈B,x<b
    · obtain ⟨l,u,hlB,huB,hlx,hxu,hgap⟩ := finite_boundary_gap hx hl hu
      have hpl : p.eval l=0 := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hlB)
      have hpu : p.eval u=0 := (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp huB)
      obtain ⟨y,hy,hdy⟩ := exists_hasDerivAt_eq_zero (hlx.trans hxu) p.continuous.continuousOn
        (hpl.trans hpu.symm) (fun y _ => p.hasDerivAt y)
      have hd : p.derivative≠0 := derivative_ne_zero_of_real_root hp hpl
      have hymem : y∈p.derivative.roots.toFinset :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr hdy)
      exact ⟨y,Finset.mem_union_left _ (Finset.mem_union_right _ hymem),
        Or.inr ⟨hx,(hgap y hy).1,(hgap y hy).2.symm⟩⟩
    · have hprof : cutProfile B x=B := by
        apply Finset.filter_eq_self.mpr
        intro b hb
        have hbx : b≤x := le_of_not_gt (fun h => hu ⟨b,hb,h⟩)
        exact lt_of_le_of_ne hbx (fun he => hx (he ▸ hb))
      refine ⟨signSampleRadius B,?_,Or.inr ⟨hx,(signSampleRadius_not_mem B).2,?_⟩⟩
      · exact Finset.mem_union_right _ (by simp [B])
      · exact hprof.trans (signSampleRadius_profiles B).2.symm
  · have hprof : cutProfile B x=∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro b hb
      exact hl ⟨b,(Finset.mem_filter.mp hb).1,(Finset.mem_filter.mp hb).2⟩
    refine ⟨-signSampleRadius B,?_,Or.inr ⟨hx,(signSampleRadius_not_mem B).1,?_⟩⟩
    · exact Finset.mem_union_right _ (by simp [B])
    · exact hprof.trans (signSampleRadius_profiles B).1.symm

/-- A fixed finite family has an actual finite set of samples realizing every
simultaneous sign pattern attained anywhere on the real line. -/
theorem exists_sample_with_same_family_signs {m : ℕ} (q : Fin m → Polynomial ℝ) (x : ℝ) :
    ∃y∈polynomialSignSamples (nonzeroFamilyProduct q),
      ∀i,SignType.sign ((q i).eval y)=SignType.sign ((q i).eval x) := by
  obtain ⟨y,hy,he | ⟨hx,hy',hprof⟩⟩ :=
    exists_sample_same_or_profile (nonzeroFamilyProduct_ne_zero q) x
  · exact ⟨y,hy,fun _ => by rw [he]⟩
  · exact ⟨y,hy,fun i => (family_signs_eq_of_product_profile q hx hy' hprof i).symm⟩

/-- The finite-sample equivalence preserves a single common witness for all
signs, including zero queried polynomials and an empty family. -/
theorem exists_family_signs_iff_sample {m : ℕ} (q : Fin m → Polynomial ℝ)
    (σ : Fin m → SignType) :
    (∃x : ℝ,∀i,SignType.sign ((q i).eval x)=σ i) ↔
      ∃y∈polynomialSignSamples (nonzeroFamilyProduct q),∀i,SignType.sign ((q i).eval y)=σ i := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,he⟩ := exists_sample_with_same_family_signs q x
    exact ⟨y,hy,fun i => (he i).trans (hx i)⟩
  · rintro ⟨y,_,hy⟩
    exact ⟨y,hy⟩

end BfgsVerification.RealAlgebraicGeometry
