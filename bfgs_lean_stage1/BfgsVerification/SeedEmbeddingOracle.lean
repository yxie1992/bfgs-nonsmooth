import BfgsVerification.SeedEmbeddingRun

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.SeedEmbedding
open SeedOrbit DeterministicLineSearch

def trialPoint (k : ℕ) (q : Fin 9) : Vec 2 :=
  orbitPoint k+trialLength q • bfgsStep (orbitMetric k) (orbitGradient k) 1

structure OracleData (F : Vec 2 → ℝ) (p : Vec 2) (t A : ℝ) : Prop extends Data F p t A where
  trial_values : ∀ k q, trialPhase q=phase k →
    F (p+t • trialPoint k q)=A+t^2*objective seedC seedD (trialPoint k q)
  trial_derivatives : ∀ k q, trialPhase q=phase k →
    HasFDerivAt F (gradientFunctional (t • SeedOrbit.gradient seedC seedD (trialActive q)))
      (p+t • trialPoint k q)

theorem translated_trial (p : Vec 2) (t : ℝ) (k : ℕ) (q : Fin 9) :
    point p t k+trialLength q • bfgsStep (orbitMetric k) (gradient t k) 1 =
      p+t • trialPoint k q := by
  simp only [point, gradient, trialPoint, bfgsStep_scale_gradient, smul_add]
  rw [smul_comm (trialLength q) t]
  abel

theorem source_trial_gradient (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) :
    coordinateGradient (objective seedC seedD) (trialPoint k q)=
      SeedOrbit.gradient seedC seedD (trialActive q) :=
  actual_coordinateGradient (hasGradient_of_active (orbit_trial_point_certificate k q hq).active)

theorem trial_predicates {F : Vec 2 → ℝ} {p : Vec 2} {t A : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k)
    (c₁ c₂ : ℝ) :
    (Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (trialLength q) ↔
      Armijo (objective seedC seedD) (orbitPoint k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)
        (orbitGradient k) c₁ (trialLength q)) ∧
    (Wolfe F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₂ (trialLength q) ↔
      Wolfe (objective seedC seedD) (orbitPoint k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)
        (orbitGradient k) c₂ (trialLength q)) := by
  have hgf := actual_coordinateGradient (h.trial_derivatives k q hq)
  have hgg := source_trial_gradient k q hq
  constructor
  · unfold Armijo
    rw [translated_trial, h.trial_values k q hq, h.values k]
    change A+t^2*objective seedC seedD (trialPoint k q) <
      A+t^2*objective seedC seedD (orbitPoint k)+
        c₁*trialLength q*dot (gradient t k) (bfgsStep (orbitMetric k) (gradient t k) 1) ↔
      objective seedC seedD (trialPoint k q) < objective seedC seedD (orbitPoint k)+
        c₁*trialLength q*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)
    simp only [gradient, bfgsStep_scale_gradient, PlanarUpdate.dot_scale_left, dot_smul_right]
    have he : A+t^2*objective seedC seedD (orbitPoint k)+
        c₁*trialLength q*(t*(t*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) 1))) =
      A+t^2*(objective seedC seedD (orbitPoint k)+
        c₁*trialLength q*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)) := by ring
    rw [he, add_lt_add_iff_left, mul_lt_mul_left (sq_pos_of_pos ht)]
  · unfold Wolfe
    rw [translated_trial, hgf]
    change c₂*dot (gradient t k) (bfgsStep (orbitMetric k) (gradient t k) 1) <
      dot (t • SeedOrbit.gradient seedC seedD (trialActive q))
        (bfgsStep (orbitMetric k) (gradient t k) 1) ↔
      c₂*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) 1) <
        dot (coordinateGradient (objective seedC seedD) (trialPoint k q))
          (bfgsStep (orbitMetric k) (orbitGradient k) 1)
    rw [hgg]
    simp only [gradient, bfgsStep_scale_gradient, PlanarUpdate.dot_scale_left, dot_smul_right]
    convert (mul_lt_mul_left (sq_pos_of_pos ht) :
      t^2*(c₂*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)) <
        t^2*dot (SeedOrbit.gradient seedC seedD (trialActive q)) (bfgsStep (orbitMetric k) (orbitGradient k) 1) ↔
      c₂*dot (orbitGradient k) (bfgsStep (orbitMetric k) (orbitGradient k) 1) <
        dot (SeedOrbit.gradient seedC seedD (trialActive q)) (bfgsStep (orbitMetric k) (orbitGradient k) 1)) using 1 <;> ring_nf

theorem source_orbit_accept {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂)
    (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) (ha : trialAccept q=true) :
    Armijo (objective seedC seedD) (orbitPoint k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)
      (orbitGradient k) c₁ (trialLength q) ∧
    Wolfe (objective seedC seedD) (orbitPoint k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)
      (orbitGradient k) c₂ (trialLength q) := by
  simp only [orbitPoint, orbitMetric, orbitGradient, bfgsStep_scale_matrix, source_direction, one_smul, ← hq]
  exact source_scaled_accept (orbitScale_pos k) hc₁ hc₁' hc₂ q ha

theorem source_orbit_reject {c₁ : ℝ} (hc₁ : 0 < c₁)
    (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) (ha : trialAccept q=false) :
    ¬ Armijo (objective seedC seedD) (orbitPoint k) (bfgsStep (orbitMetric k) (orbitGradient k) 1)
      (orbitGradient k) c₁ (trialLength q) := by
  simp only [orbitPoint, orbitMetric, orbitGradient, bfgsStep_scale_matrix, source_direction, one_smul, ← hq]
  exact source_scaled_reject (orbitScale_pos k) hc₁ q ha

theorem trial_accept {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ c₂ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1/3) (hc₂ : 0 < c₂)
    (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) (ha : trialAccept q=true) :
    Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (trialLength q) ∧
    Wolfe F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₂ (trialLength q) := by
  have hs := source_orbit_accept hc₁ hc₁' hc₂ k q hq ha
  exact ⟨((trial_predicates h ht k q hq c₁ c₂).1).mpr hs.1,
    ((trial_predicates h ht k q hq c₁ c₂).2).mpr hs.2⟩

theorem trial_reject {F : Vec 2 → ℝ} {p : Vec 2} {t A c₁ : ℝ}
    (h : OracleData F p t A) (ht : 0 < t) (hc₁ : 0 < c₁)
    (k : ℕ) (q : Fin 9) (hq : trialPhase q=phase k) (ha : trialAccept q=false) :
    ¬ Armijo F (point p t k) (bfgsStep (orbitMetric k) (gradient t k) 1) (gradient t k) c₁ (trialLength q) := by
  rw [(trial_predicates h ht k q hq c₁ 0).1]
  exact source_orbit_reject hc₁ k q hq ha

end BfgsVerification.SeedEmbedding
