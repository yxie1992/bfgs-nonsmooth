import BfgsVerification.DeterministicLineSearch
noncomputable section
namespace BfgsVerification.NonStrictLineSearch
def Armijo {n : ℕ} (F : Vec n → ℝ) (x p g : Vec n) (c₁ a : ℝ) : Prop :=
  F (x+a • p) ≤ F x+c₁*a*dot g p

def Wolfe {n : ℕ} (F : Vec n → ℝ) (x p g : Vec n) (c₂ a : ℝ) : Prop :=
  c₂*dot g p ≤ dot (coordinateGradient F (x+a • p)) p

def nextTrial (l : ℝ) (h : Option ℝ) : ℝ :=
  match h with
  | none => 2*l
  | some u => (l+u)/2

/-- A fuel-bounded prefix of the exact lower/upper bracket search. Success records
the accepted length and every attempted length in order; exhausting fuel is failure.
A success theorem therefore proves finite termination of the specified search. -/
def search {n : ℕ} (F : Vec n → ℝ) (x p g : Vec n) (c₁ c₂ : ℝ)
    (fuel : ℕ) (l : ℝ) (h : Option ℝ) (a : ℝ) : Option ℝ × List ℝ := by
  classical
  exact match fuel with
  | 0 => (none,[])
  | fuel+1 =>
    if Armijo F x p g c₁ a then
      if Wolfe F x p g c₂ a then (some a,[a])
      else let r := search F x p g c₁ c₂ fuel a h (nextTrial a h)
           (r.1,a::r.2)
    else let r := search F x p g c₁ c₂ fuel l (some a) (nextTrial l (some a))
         (r.1,a::r.2)
termination_by fuel

/-- Start from the actual derivative and the ordinary full-BFGS search direction. -/
def fromMetric {n : ℕ} (F : Vec n → ℝ) (x : Vec n) (H : Mat n) (c₁ c₂ : ℝ) (fuel : ℕ) :
    Option ℝ × List ℝ :=
  search F x (bfgsStep H (coordinateGradient F x) 1) (coordinateGradient F x) c₁ c₂ fuel 0 none 1

theorem search_accept {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ a l : ℝ}
    {h : Option ℝ} (fuel : ℕ) (ha : Armijo F x p g c₁ a) (hw : Wolfe F x p g c₂ a) :
    search F x p g c₁ c₂ (fuel+1) l h a=(some a,[a]) := by
  rw [search,if_pos ha,if_pos hw]

theorem search_armijo_reject {n : ℕ} {F : Vec n → ℝ} {x p g : Vec n} {c₁ c₂ a l : ℝ}
    {h : Option ℝ} (fuel : ℕ) (ha : ¬ Armijo F x p g c₁ a) :
    search F x p g c₁ c₂ (fuel+1) l h a=
      let r := search F x p g c₁ c₂ fuel l (some a) ((l+a)/2)
      (r.1,a::r.2) := by
  rw [search,if_neg ha]
  rfl


end BfgsVerification.NonStrictLineSearch
