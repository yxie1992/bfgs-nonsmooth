import BfgsVerification.PlanarMaxRegular
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Order.Monotone.Union

noncomputable section
open scoped Topology ContDiff
open Set Filter Matrix
namespace BfgsVerification.RidgeSupersession

/-- C2 profiles with positive second derivative away from one point are
strictly convex on the whole line, including intervals crossing that point. -/
theorem strictConvex_of_second_pos_except {a : ℝ → ℝ} (ha : ContDiff ℝ 2 a)
    (u : ℝ) (hpos : ∀x,x≠u → 0<deriv (deriv a) x) : StrictConvexOn ℝ univ a := by
  have hc := ha.continuous_deriv (by norm_num)
  have hleft : StrictMonoOn (deriv a) (Iic u) :=
    strictMonoOn_of_deriv_pos (convex_Iic u) hc.continuousOn (by
      intro x hx
      rw [interior_Iic] at hx
      exact hpos x (ne_of_lt hx))
  have hright : StrictMonoOn (deriv a) (Ici u) :=
    strictMonoOn_of_deriv_pos (convex_Ici u) hc.continuousOn (by
      intro x hx
      rw [interior_Ici] at hx
      exact hpos x (ne_of_gt hx))
  exact (hleft.Iic_union_Ici hright).strictConvexOn_univ_of_deriv ha.continuous

def profile (a b : ℝ → ℝ) (p q : ℝ) (u : ℝ) : ℝ := (q*a u+p*b u)/(p+q)
def ridge (a b : ℝ → ℝ) (p q : ℝ) (u : ℝ) : ℝ := (b u-a u)/(p+q)
def branch (a b : ℝ → ℝ) (p q : ℝ) : Fin 2 → Vec 2 → ℝ :=
  ![fun x => a (x 0)+p*x 1,fun x => b (x 0)-q*x 1]
def objective (a b : ℝ → ℝ) (p q : ℝ) (x : Vec 2) : ℝ :=
  max (a (x 0)+p*x 1) (b (x 0)-q*x 1)
def optimizer (a b : ℝ → ℝ) (p q u : ℝ) : Vec 2 := ![u,ridge a b p q u]

theorem branch_convex {a b : ℝ → ℝ} (ha : ConvexOn ℝ univ a) (hb : ConvexOn ℝ univ b)
    (p q : ℝ) (i : Fin 2) : ConvexOn ℝ univ (branch a b p q i) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ α β hα hβ hsum
  have hA := ha.2 (mem_univ (x 0)) (mem_univ (y 0)) hα hβ hsum
  have hB := hb.2 (mem_univ (x 0)) (mem_univ (y 0)) hα hβ hsum
  simp only [smul_eq_mul] at hA hB
  fin_cases i <;> norm_num [branch,Pi.smul_apply,Pi.add_apply,smul_eq_mul] <;> nlinarith

theorem objective_convex {a b : ℝ → ℝ} (ha : ConvexOn ℝ univ a) (hb : ConvexOn ℝ univ b)
    (p q : ℝ) : ConvexOn ℝ univ (objective a b p q) :=
  (branch_convex ha hb p q 0).sup (branch_convex ha hb p q 1)

theorem ridge_values {a b : ℝ → ℝ} {p q : ℝ} (hpq : p+q≠0) (u : ℝ) :
    a u+p*ridge a b p q u=profile a b p q u ∧
    b u-q*ridge a b p q u=profile a b p q u := by
  constructor <;> dsimp [ridge,profile] <;> field_simp <;> ring

theorem objective_optimizer {a b : ℝ → ℝ} {p q : ℝ} (hpq : p+q≠0) (u : ℝ) :
    objective a b p q (optimizer a b p q u)=profile a b p q u := by
  simpa [objective,optimizer,(ridge_values hpq u).1,(ridge_values hpq u).2]

theorem profile_le_objective {a b : ℝ → ℝ} {p q : ℝ} (hp : 0<p) (hq : 0<q)
    (x : Vec 2) : profile a b p q (x 0) ≤ objective a b p q x := by
  have h0 := le_max_left (a (x 0)+p*x 1) (b (x 0)-q*x 1)
  have h1 := le_max_right (a (x 0)+p*x 1) (b (x 0)-q*x 1)
  apply (div_le_iff₀ (add_pos hp hq)).mpr
  change q*a (x 0)+p*b (x 0) ≤ max (a (x 0)+p*x 1) (b (x 0)-q*x 1)*(p+q)
  nlinarith

theorem optimizer_minimum {a b : ℝ → ℝ} {p q u : ℝ} (hp : 0<p) (hq : 0<q)
    (hmin : ∀t,profile a b p q u ≤ profile a b p q t) (x : Vec 2) :
    objective a b p q (optimizer a b p q u) ≤ objective a b p q x := by
  rw [objective_optimizer (add_pos hp hq).ne']
  exact (hmin (x 0)).trans (profile_le_objective hp hq x)

theorem optimizer_unique {a b : ℝ → ℝ} {p q u : ℝ} (hp : 0<p) (hq : 0<q)
    (hmin : ∀t,profile a b p q u ≤ profile a b p q t)
    (hunique : ∀t,profile a b p q t=profile a b p q u → t=u)
    (x : Vec 2) (hx : objective a b p q x=objective a b p q (optimizer a b p q u)) :
    x=optimizer a b p q u := by
  have hv := objective_optimizer (a:=a) (b:=b) (add_pos hp hq).ne' u
  have hu : x 0=u := hunique _ (le_antisymm
    ((profile_le_objective hp hq x).trans (hx.trans hv).le) (hmin (x 0)))
  have h0 : a u+p*x 1 ≤ profile a b p q u := by
    have h := le_max_left (a (x 0)+p*x 1) (b (x 0)-q*x 1)
    change a (x 0)+p*x 1 ≤ objective a b p q x at h
    rwa [hu,hx,hv] at h
  have h1 : b u-q*x 1 ≤ profile a b p q u := by
    have h := le_max_right (a (x 0)+p*x 1) (b (x 0)-q*x 1)
    change b (x 0)-q*x 1 ≤ objective a b p q x at h
    rwa [hu,hx,hv] at h
  obtain ⟨hr0,hr1⟩ := ridge_values (a:=a) (b:=b) (add_pos hp hq).ne' u
  have hv' : x 1=ridge a b p q u := by nlinarith
  ext i
  fin_cases i <;> simp [optimizer,hu,hv']

end BfgsVerification.RidgeSupersession
