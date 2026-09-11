import BfgsVerification.TransportedCertificateRun
import BfgsVerification.CompactConvergence

/-! Module T: value convergence from objective-only transported certificates.
Compactness derives gradient bounds, Armijo derives summability, monotonicity
derives the finite value limit, and actual accepted pairs derive eventual eligibility. -/

noncomputable section
open scoped BigOperators Topology
open Matrix Filter Set

namespace BfgsVerification.AdmissibleBFGSRun

open TransportedCertificate
variable {n : ℕ} {F : Vec n → ℝ} (R : AdmissibleBFGSRun n F)

/-- Module T's positive-band certificate assumptions force objective convergence.
The compact set may be any set containing the accepted iterates; its sublevel
specialization below derives containment from the starting point and Armijo. -/
theorem transported_certificate_values (K : Set (Vec n)) (hK : IsCompact K)
    (hxK : ∀ k, R.x k ∈ K) (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (hcert : HasBandCertificates F K (F xstar) R.c₁ R.c₂) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) := by
  have hsum := R.summable_predicted_decreases_of_lower_bound (F xstar) (fun k => hmin (R.x k))
  obtain ⟨G, hG, hg⟩ := R.bounded_gradients_of_compact_set K hK hxK
  have hbounded : BddBelow (Set.range (fun k => F (R.x k))) := by
    refine ⟨F xstar, ?_⟩
    rintro z ⟨k, rfl⟩
    exact hmin _
  let ℓ := ⨅ k, F (R.x k)
  have hlim : Tendsto (fun k => F (R.x k)) atTop (𝓝 ℓ) :=
    tendsto_atTop_ciInf R.objective_antitone hbounded
  have hfloor : F xstar ≤ ℓ := le_ciInf (fun k => hmin (R.x k))
  have hlevels : ∀ k, ℓ ≤ F (R.x k) := fun k => ciInf_le hbounded k
  have hvalue : ℓ = F xstar := by
    by_contra hne
    have hpos : F xstar < ℓ := lt_of_le_of_ne hfloor (Ne.symm hne)
    let η := (ℓ - F xstar) / 2
    have hη : 0 < η := by dsimp only [η]; linarith
    have hband : ∀ k, R.x k ∈ positiveBand F K (F xstar) η := by
      intro k
      refine ⟨hxK k, ?_⟩
      dsimp only [η]
      linarith [hlevels k]
    obtain ⟨C⟩ := hcert η hη ⟨R.x 0, hband 0⟩
    have hevent : ∀ᶠ k in atTop, R.d k < C.δ :=
      hsum.tendsto_atTop_zero.eventually (gt_mem_nhds C.delta_pos)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
    exact (R.shift J).band_certificate_incompatible C (fun k => hband (J + k))
      (fun k => (hJ (J + k) (Nat.le_add_right J k)).le)
      G hG (fun k => hg (J + k)) (R.shift_summable_d hsum J)
  simpa only [hvalue] using hlim

/-- Source T's compact-sublevel value theorem, for every ordinary admissible run
starting in the sublevel. All eligible-pair and small-step conditions remain objective-only. -/
theorem transported_certificate_values_on_sublevel (b : ℝ)
    (hK : IsCompact {x : Vec n | F x ≤ b}) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (hstart : F (R.x 0) ≤ b)
    (hcert : HasBandCertificates F {x | F x ≤ b} (F xstar) R.c₁ R.c₂) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) :=
  R.transported_certificate_values _ hK
    (fun k => (R.objective_le_initial k).trans hstart) xstar hmin hcert

/-- Uniqueness upgrades the certificate's proved value convergence to convergence
of the whole accepted iterate sequence. No iterate convergence is assumed. -/
theorem transported_certificate_iterates_of_unique_minimizer
    (K : Set (Vec n)) (hK : IsCompact K) (hxK : ∀ k, R.x k ∈ K)
    (xstar : Vec n) (hmin : ∀ x, F xstar ≤ F x)
    (hunique : ∀ x, F x = F xstar → x = xstar)
    (hcert : HasBandCertificates F K (F xstar) R.c₁ R.c₂) :
    Tendsto R.x atTop (𝓝 xstar) :=
  R.iterates_tendsto_unique_min_of_values xstar hmin hunique
    (R.transported_certificate_values K hK hxK xstar hmin hcert)

/-- Module T's complete compact-sublevel conclusion: value and solution-set
convergence, and whole-sequence convergence when the minimizer is unique. -/
theorem transported_certificate_convergence_on_sublevel (b : ℝ)
    (hK : IsCompact {x : Vec n | F x ≤ b}) (xstar : Vec n)
    (hmin : ∀ x, F xstar ≤ F x) (hstart : F (R.x 0) ≤ b)
    (hcert : HasBandCertificates F {x | F x ≤ b} (F xstar) R.c₁ R.c₂) :
    Tendsto (fun k => F (R.x k)) atTop (𝓝 (F xstar)) ∧
      Tendsto (fun k => Metric.infDist (R.x k) (argmin F)) atTop (𝓝 0) ∧
      ((∀ x, F x = F xstar → x = xstar) → Tendsto R.x atTop (𝓝 xstar)) := by
  have hvalues := R.transported_certificate_values_on_sublevel b hK xstar hmin hstart hcert
  refine ⟨hvalues, R.distance_to_argmin_of_values xstar hmin hK
    (fun k => (R.objective_le_initial k).trans hstart) hvalues, ?_⟩
  intro hunique
  exact R.iterates_tendsto_unique_min_of_values xstar hmin hunique hvalues

end BfgsVerification.AdmissibleBFGSRun
