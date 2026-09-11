import BfgsVerification.StablePositiveDirection

/-! Exact constructive dynamics criteria. Application to L's actual normalized
return map still requires its verified derivative splitting and oracle agreement. -/
noncomputable section
open scoped Topology
open Set Filter
namespace BfgsVerification.LocalStableOrbit

def StableOrbitTarget : Prop :=
  ∀ (A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (L : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ))
    (T : (Fin 2 → ℝ)×(Fin 3 → ℝ) → (Fin 2 → ℝ)×(Fin 3 → ℝ)),
    T 0=0 → HasStrictFDerivAt T (A.prodMap L.toContinuousLinearMap) 0 →
    ‖A‖<1 → ‖L.symm.toContinuousLinearMap‖<1 → ∀ r : ℝ, 0<r →
    ∃ R : ℝ, 0<R ∧ ∀ a : Fin 2 → ℝ, ‖a‖≤R →
      ∃ w : ℕ → (Fin 2 → ℝ)×(Fin 3 → ℝ), (∀ n, ‖w n‖≤r) ∧
        Tendsto w atTop (𝓝 0) ∧ (w 0).1=a ∧ ∀ n, w (n+1)=T (w n)

def PositiveStableOrbitTarget : Prop :=
  ∀ (A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (L : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ))
    (T : (Fin 2 → ℝ)×(Fin 3 → ℝ) → (Fin 2 → ℝ)×(Fin 3 → ℝ)),
    T 0=0 → HasStrictFDerivAt T (A.prodMap L.toContinuousLinearMap) 0 →
    ‖A‖<1 → ‖L.symm.toContinuousLinearMap‖<1 →
    ∀ (lambda : (Fin 2 → ℝ) →L[ℝ] ℝ) (e : Fin 2 → ℝ), 0<lambda e →
      ∀ r : ℝ, 0<r → ∃ w : ℕ → (Fin 2 → ℝ)×(Fin 3 → ℝ),
        (∀ n, ‖w n‖≤r) ∧ Tendsto w atTop (𝓝 0) ∧
        0<lambda (w 0).1 ∧ w 0≠0 ∧ ∀ n, w (n+1)=T (w n)

theorem stableOrbit : StableOrbitTarget := by
  intro A L T hT0 hT hA hB r hr
  exact local_stable_orbits A L T hT0 hT hA hB hr

theorem positiveStableOrbit : PositiveStableOrbitTarget := by
  intro A L T hT0 hT hA hB lambda e he r hr
  exact positive_stable_direction A L T hT0 hT hA hB lambda e he hr

end BfgsVerification.LocalStableOrbit
