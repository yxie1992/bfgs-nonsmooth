import BfgsVerification.NonStrictLineSearch
import BfgsVerification.ScaledCopyRun
import BfgsVerification.AffineWhiteningSearch

/-!
# Non-strict search transfers

Non-strict counterparts of the generic search-transfer results used by the
lower-curvature construction:

* agreement on the actual finite search history (`FiniteSearchTransfer`),
* translated and scaled local copies (`TranslatedSearch`, `ScaledCopyRun`),
* fixed affine whitening (`AffineWhiteningSearch`).

Each proof follows the strict original with `≤` in place of `<`; the strict
library files are unchanged.
-/

noncomputable section
open scoped Topology
open Set Filter Matrix

namespace BfgsVerification.NonStrictLineSearch

/-- Agreement of both non-strict comparisons on the source search's actual
finite history preserves the entire branching non-strict search. -/
theorem search_history_congr {n : ℕ} (Q F : Vec n → ℝ) (x p g u v h : Vec n)
    (c₁ c₂ : ℝ) (fuel : ℕ) (l : ℝ) (upper : Option ℝ) (a : ℝ)
    (hc : ∀b∈(search Q x p g c₁ c₂ fuel l upper a).2,
      (Armijo F u v h c₁ b↔Armijo Q x p g c₁ b) ∧
      (Wolfe F u v h c₂ b↔Wolfe Q x p g c₂ b)) :
    search F u v h c₁ c₂ fuel l upper a=search Q x p g c₁ c₂ fuel l upper a := by
  induction fuel generalizing l upper a with
  | zero => simp only [search]
  | succ fuel ih =>
    by_cases hA : Armijo Q x p g c₁ a
    · by_cases hW : Wolfe Q x p g c₂ a
      · have he : search Q x p g c₁ c₂ (fuel+1) l upper a=(some a,[a]) := search_accept fuel hA hW
        have ha := hc a (by rw [he]; simp)
        rw [search_accept fuel (ha.1.mpr hA) (ha.2.mpr hW),he]
      · have he : search Q x p g c₁ c₂ (fuel+1) l upper a=
          let r := search Q x p g c₁ c₂ fuel a upper (nextTrial a upper)
          (r.1,a::r.2) := by rw [search,if_pos hA,if_neg hW]
        have ha := hc a (by rw [he]; simp)
        have hh := ih a upper (nextTrial a upper) (fun b hb => hc b (by rw [he]; exact List.mem_cons_of_mem a hb))
        rw [search,if_pos (ha.1.mpr hA),if_neg (fun hw => hW (ha.2.mp hw)),hh]
        exact he.symm
    · have he : search Q x p g c₁ c₂ (fuel+1) l upper a=
          let r := search Q x p g c₁ c₂ fuel l (some a) ((l+a)/2)
          (r.1,a::r.2) := search_armijo_reject fuel hA
      have ha := hc a (by rw [he]; simp)
      have hh := ih l (some a) ((l+a)/2) (fun b hb => hc b (by rw [he]; exact List.mem_cons_of_mem a hb))
      rw [search_armijo_reject fuel (fun hw => hA (ha.1.mp hw)),hh]
      exact he.symm

end BfgsVerification.NonStrictLineSearch

namespace BfgsVerification.TranslatedRun

variable {n : ℕ} {Q F : Vec n → ℝ}

theorem nonstrict_translated_comparisons {p x d g : Vec n} {t A a c₁ c₂ : ℝ} (ht : t≠0)
    (hbase : F (p+t • x)=A+t^2*Q x)
    (htrial : F (p+t • (x+a • d))=A+t^2*Q (x+a • d))
    (hgrad : coordinateGradient F (p+t • (x+a • d))=t • coordinateGradient Q (x+a • d)) :
    (NonStrictLineSearch.Armijo F (p+t • x) (t • d) (t • g) c₁ a↔
      NonStrictLineSearch.Armijo Q x d g c₁ a) ∧
    (NonStrictLineSearch.Wolfe F (p+t • x) (t • d) (t • g) c₂ a↔
      NonStrictLineSearch.Wolfe Q x d g c₂ a) := by
  have hs : 0<t^2 := sq_pos_of_ne_zero ht
  have hp (v : Vec n) : dot (t • v) (t • d)=t^2*dot v d := by
    rw [dot_smul_right,PlanarUpdate.dot_scale_left]
    ring
  constructor
  · simp only [NonStrictLineSearch.Armijo,translated_trial,hbase,htrial,hp]
    have he : A+t^2*Q x+c₁*a*(t^2*dot g d)=A+t^2*(Q x+c₁*a*dot g d) := by ring
    rw [he,add_le_add_iff_left,mul_le_mul_left hs]
  · simp only [NonStrictLineSearch.Wolfe,translated_trial,hgrad,hp]
    rw [show c₂*(t^2*dot g d)=t^2*(c₂*dot g d) from by ring,mul_le_mul_left hs]

/-- Non-strict form of `local_model_search`: local identity and actual
differentiability are required only at the source search's attempted points. -/
theorem nonstrict_local_model_search {U : Set (Vec n)} (hU : IsOpen U)
    {p x g : Vec n} {H : Mat n} {t A c₁ c₂ : ℝ} (ht : t≠0) (hx : x∈U)
    (hg : HasFDerivAt Q (gradientFunctional g) x) (fuel : ℕ)
    (hmodel : ∀y∈U,F (p+t • y)=A+t^2*Q y)
    (hqueries : ∀a∈(NonStrictLineSearch.fromMetric Q x H c₁ c₂ fuel).2,
      x+a • bfgsStep H g 1∈U ∧ DifferentiableAt ℝ Q (x+a • bfgsStep H g 1)) :
    NonStrictLineSearch.fromMetric F (p+t • x) H c₁ c₂ fuel=
      NonStrictLineSearch.fromMetric Q x H c₁ c₂ fuel := by
  have hgf := local_model_hasGradient hU ht hx hmodel hg
  have hcg := DeterministicLineSearch.actual_coordinateGradient hg
  have hcf := DeterministicLineSearch.actual_coordinateGradient hgf
  unfold NonStrictLineSearch.fromMetric
  rw [hcg,hcf,bfgsStep_scale_gradient]
  apply NonStrictLineSearch.search_history_congr
  intro a ha
  have hmem : a∈(NonStrictLineSearch.fromMetric Q x H c₁ c₂ fuel).2 := by
    simpa only [NonStrictLineSearch.fromMetric,hcg] using ha
  obtain ⟨hq,hd⟩ := hqueries a hmem
  exact nonstrict_translated_comparisons ht (hmodel x hx) (hmodel _ hq)
    (translated_query_gradient hU ht hq hmodel (hasFDerivAt_coordinateGradient hd))

end BfgsVerification.TranslatedRun

namespace BfgsVerification.ScaledCopy.Data
open LScalarGeometric

variable {n : ℕ} {Q F : Vec n → ℝ} {c : Vec n} {C : ℝ} {U : Set (Vec n)}

theorem nonstrict_search_transfer (D : Data Q F c C U) (R : AdmissibleBFGSRun n Q) (hx : ∀k,R.x k∈U)
    (fuel : ℕ) (hq : ∀k,∀a∈(NonStrictLineSearch.fromMetric Q (R.x k) (R.H k) R.c₁ R.c₂ fuel).2,
      R.x k+a • bfgsStep (R.H k) (R.g k) 1∈U ∧
      DifferentiableAt ℝ Q (R.x k+a • bfgsStep (R.H k) (R.g k) 1)) (m k : ℕ) :
    NonStrictLineSearch.fromMetric F ((D.run R hx m).x k) ((D.run R hx m).H k) R.c₁ R.c₂ fuel=
      NonStrictLineSearch.fromMetric Q (R.x k) (R.H k) R.c₁ R.c₂ fuel :=
  TranslatedRun.nonstrict_local_model_search D.open_domain (scale_pos m).ne' (hx k) (R.hasGradient k) fuel
    (D.model_offset m) (hq k)

end BfgsVerification.ScaledCopy.Data

namespace BfgsVerification.AffineWhitening
open AffineProjection

variable {n : ℕ}

theorem nonstrict_armijo_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x p g : Vec n) (c a : ℝ) :
    NonStrictLineSearch.Armijo (objective A F) (point A x) (point A p) (gradient A g) c a ↔
      NonStrictLineSearch.Armijo F x p g c a := by
  have hq : point A x+a • point A p=point A (x+a • p) := by
    simp only [point,Matrix.mulVec_add,Matrix.mulVec_smul]
  simp only [NonStrictLineSearch.Armijo,hq,objective,map_point A hA,dot_gradient_point A hA]

theorem nonstrict_wolfe_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x p g : Vec n) (c a : ℝ) :
    NonStrictLineSearch.Wolfe (objective A F) (point A x) (point A p) (gradient A g) c a ↔
      NonStrictLineSearch.Wolfe F x p g c a := by
  have hq : point A x+a • point A p=point A (x+a • p) := by
    simp only [point,Matrix.mulVec_add,Matrix.mulVec_smul]
  simp only [NonStrictLineSearch.Wolfe,hq,coordinateGradient_equiv A hA,dot_gradient_point A hA]

theorem nonstrict_search_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x p g : Vec n) (c₁ c₂ : ℝ) (fuel : ℕ) (l : ℝ) (h : Option ℝ) (a : ℝ) :
    NonStrictLineSearch.search (objective A F) (point A x) (point A p) (gradient A g) c₁ c₂ fuel l h a=
      NonStrictLineSearch.search F x p g c₁ c₂ fuel l h a :=
  NonStrictLineSearch.search_history_congr F (objective A F) x p g (point A x) (point A p) (gradient A g)
    c₁ c₂ fuel l h a
    (fun b _ => ⟨nonstrict_armijo_equiv A hA F x p g c₁ b,nonstrict_wolfe_equiv A hA F x p g c₂ b⟩)

/-- Every non-strict decision and every attempted length is unchanged by a fixed
whitening, for arbitrary fuel. -/
theorem nonstrict_fromMetric_equiv (A : Mat n) (hA : A.det≠0) (F : Vec n → ℝ)
    (x : Vec n) (H : Mat n) (c₁ c₂ : ℝ) (fuel : ℕ) :
    NonStrictLineSearch.fromMetric (objective A F) (point A x) (metric A H) c₁ c₂ fuel=
      NonStrictLineSearch.fromMetric F x H c₁ c₂ fuel := by
  simp only [NonStrictLineSearch.fromMetric,coordinateGradient_equiv A hA,step_equiv A hA,
    nonstrict_search_equiv A hA]

end BfgsVerification.AffineWhitening
