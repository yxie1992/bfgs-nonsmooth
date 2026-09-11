import BfgsVerification.NormalSpikeVariableConvex

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.NormalSpike
open FixedNormal

theorem dot_add_smul {n : ℕ} (d x a : Vec n) (t : ℝ) :
    dot d (x+t • a) = dot d x+t*dot d a := by
  change d ⬝ᵥ (x+t • a) = d ⬝ᵥ x+t*(d ⬝ᵥ a)
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]

theorem dot_sub_smul {n : ℕ} (d x a : Vec n) (t : ℝ) :
    dot d (x-t • a) = dot d x-t*dot d a := by
  change d ⬝ᵥ (x-t • a) = d ⬝ᵥ x-t*(d ⬝ᵥ a)
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem quadratic_central_sum {n : ℕ} (x a : Vec n) (t : ℝ) :
    quadratic (x+t • a)+quadratic (x-t • a) = 2*quadratic x+t^2*sqNorm a := by
  have hp := sqNorm_sub_smul x a (-t)
  have hn := sqNorm_sub_smul x a t
  simp only [neg_smul, sub_neg_eq_add] at hp
  dsimp [quadratic]
  nlinarith

theorem variable_central_difference {n : ℕ} {a c : Vec n} (ha : sqNorm a = 1)
    (hc : dot a c = 0) (x : Vec n) (hx : dot a x = 0)
    (hw : 0 ≤ 1+dot c x) (t : ℝ) :
    variableObjective a c (x+t • a)+variableObjective a c (x-t • a)-2*variableObjective a c x -
      (variableObjective a c (t • a)+variableObjective a c (-t • a)-2*variableObjective a c 0) =
        2*dot c x*|t| := by
  have haa : dot a a = 1 := by simpa only [dot, sqNorm, pow_two] using ha
  have hca : dot c a = 0 := by
    change c ⬝ᵥ a = 0
    rw [dotProduct_comm]
    exact hc
  have hxp := quadratic_central_sum x a t
  have h0p := quadratic_central_sum (0 : Vec n) a t
  simp only [zero_add, zero_sub] at h0p
  have hsq : quadratic (t • a)+quadratic (-t • a) = t^2*sqNorm a := by
    simpa only [neg_smul, quadratic, sqNorm, Pi.zero_apply, ne_eq, zero_pow,
      OfNat.ofNat_ne_zero, not_false_eq_true, Finset.sum_const_zero, mul_zero, zero_add] using h0p
  simp only [variableObjective, dot_add_smul, dot_sub_smul, dot_smul_right,
    hx, haa, hca, mul_one, mul_zero, zero_add, sub_zero, zero_sub]
  have hr0 : sourcePrimitive 0 = 0 := by simp [sourcePrimitive]
  simp only [show dot a (0 : Vec n) = 0 by simp [dot], show dot c (0 : Vec n) = 0 by simp [dot],
    add_zero, mul_zero, abs_zero, hr0]
  rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_neg]
  simp only [one_mul, abs_neg]
  have hq0 : quadratic (0 : Vec n) = 0 := by simp [quadratic, sqNorm]
  rw [hq0]
  linarith

theorem variableObjective_no_local_smooth_scalar_split {n : ℕ} {a c : Vec n}
    (ha : sqNorm a = 1) (hc : dot a c = 0) (hcne : c ≠ 0)
    {U : Set (Vec n)} (hU : IsOpen U) (h0 : (0 : Vec n) ∈ U)
    (S : Vec n → ℝ) (h : ℝ → ℝ) (hS : DifferentiableOn ℝ S U)
    (hrep : ∀ x ∈ U, variableObjective a c x = S x + h (dot a x)) : False := by
  have hcu : ∀ᶠ t : ℝ in 𝓝 0, t • c ∈ U := by
    have ht : Tendsto (fun t : ℝ => t • c) (𝓝 0) (𝓝 (0 : Vec n)) := by
      have hpath : Continuous (fun t : ℝ => t • c) := by fun_prop
      simpa only [zero_smul] using hpath.tendsto 0
    exact ht.eventually (hU.mem_nhds h0)
  have hex : ∃ δ : ℝ, δ • c ∈ U ∧ 0 < δ := by
    have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ • c ∈ U ∧ δ ∈ Ioi 0 :=
      (hcu.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    exact he.exists
  obtain ⟨δ, hxU, hδ⟩ := hex
  let x : Vec n := δ • c
  have hx : dot a x = 0 := by dsimp [x]; rw [dot_smul_right, hc, mul_zero]
  have hcc : dot c c = sqNorm c := by simp only [dot, sqNorm, pow_two]
  have hcpos : 0 < sqNorm c := lt_of_le_of_ne (sqNorm_nonneg c)
    (Ne.symm (fun hz => hcne ((CertificateGeometry.sqNorm_eq_zero_iff c).mp hz)))
  have hcx : 0 < dot c x := by dsimp [x]; rw [dot_smul_right, hcc]; exact mul_pos hδ hcpos
  have hxU' : x ∈ U := hxU
  have hxS : DifferentiableAt ℝ S x := (hS x hxU').differentiableAt (hU.mem_nhds hxU')
  have h0S : DifferentiableAt ℝ S 0 := (hS 0 h0).differentiableAt (hU.mem_nhds h0)
  have ht : DifferentiableAt ℝ (fun t : ℝ => t • a) 0 := differentiableAt_id.smul_const a
  have hnt : DifferentiableAt ℝ (fun t : ℝ => -t • a) 0 := differentiableAt_id.neg.smul_const a
  have hxp : DifferentiableAt ℝ (fun t : ℝ => x+t • a) 0 := (differentiableAt_const x).add ht
  have hxm : DifferentiableAt ℝ (fun t : ℝ => x-t • a) 0 := (differentiableAt_const x).sub ht
  let C : ℝ → ℝ := fun t => S (x+t • a)+S (x-t • a)-2*S x -
    (S (t • a)+S (-t • a)-2*S 0)
  have hDC : DifferentiableAt ℝ C 0 := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => S (x+t • a)) 0 := by
      apply DifferentiableAt.comp (0 : ℝ) ?_ hxp
      simpa only [zero_smul, add_zero] using hxS
    have h2 : DifferentiableAt ℝ (fun t : ℝ => S (x-t • a)) 0 := by
      apply DifferentiableAt.comp (0 : ℝ) ?_ hxm
      simpa only [zero_smul, sub_zero] using hxS
    have h3 : DifferentiableAt ℝ (fun t : ℝ => S (t • a)) 0 := by
      apply DifferentiableAt.comp (0 : ℝ) ?_ ht
      simpa only [zero_smul] using h0S
    have h4 : DifferentiableAt ℝ (fun t : ℝ => S (-t • a)) 0 := by
      apply DifferentiableAt.comp (0 : ℝ) ?_ hnt
      simpa only [neg_zero, zero_smul] using h0S
    exact ((h1.add h2).sub_const _).sub ((h3.add h4).sub_const _)
  have hu1 : ∀ᶠ t : ℝ in 𝓝 0, x+t • a ∈ U := by
    apply hxp.continuousAt.eventually
    simpa using hU.mem_nhds hxU'
  have hu2 : ∀ᶠ t : ℝ in 𝓝 0, x-t • a ∈ U := by
    apply hxm.continuousAt.eventually
    simpa using hU.mem_nhds hxU'
  have hu3 : ∀ᶠ t : ℝ in 𝓝 0, t • a ∈ U := by
    apply ht.continuousAt.eventually
    simpa using hU.mem_nhds h0
  have hu4 : ∀ᶠ t : ℝ in 𝓝 0, -t • a ∈ U := by
    apply hnt.continuousAt.eventually
    simpa using hU.mem_nhds h0
  have hEq : C =ᶠ[𝓝 0] (fun t : ℝ => 2*dot c x*|t|) := by
    filter_upwards [hu1, hu2, hu3, hu4] with t ht1 ht2 ht3 ht4
    have he := variable_central_difference ha hc x hx (by linarith) t
    rw [hrep _ ht1, hrep _ ht2, hrep _ hxU', hrep _ ht3, hrep _ ht4, hrep _ h0] at he
    have haa : dot a a = 1 := by simpa only [dot, sqNorm, pow_two] using ha
    simp only [dot_add_smul, dot_sub_smul, dot_smul_right, hx, haa, mul_one, zero_add,
      zero_sub, show dot a (0 : Vec n) = 0 by simp [dot]] at he
    dsimp [C]
    linarith
  have hDa : DifferentiableAt ℝ (fun t : ℝ => 2*dot c x*|t|) 0 :=
    hDC.congr_of_eventuallyEq hEq.symm
  have hz : 2*dot c x ≠ 0 := by positivity
  have hdabs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    convert hDa.const_mul ((2*dot c x)⁻¹) using 1
    ext t
    field_simp
  exact not_differentiableAt_abs_zero hdabs

end BfgsVerification.NormalSpike
