import BfgsVerification.ParabolicExampleScale

noncomputable section
open scoped Topology
open Set BfgsVerification TransportedCertificate Parabolic.Example

example : ContinuousOn sourceScale {x | 0 < objective x} := sourceScale_continuousOn

example : ∃ c : ℝ, 0 < c ∧ ∀ x, 0 < objective x → sourceScale x = c*family.calibratedScale x :=
  ⟨sourceNormalization, sourceNormalization_pos, fun _ hx => sourceScale_eq_normalized hx⟩

example {K : Set (Vec 2)} (hK : IsCompact K) {η c₁ c₂ : ℝ}
    (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hc₂ : c₂ < 1) :
    ∃ B : BandCertificate objective K 0 c₁ c₂ η,
      ∀ x, B.W x = outer (sourceScale x • Parabolic.Family.radialDirection x)
        (sourceScale x • Parabolic.Family.radialDirection x) :=
  exists_source_bandCertificate hK hη hc₁ hc₂
