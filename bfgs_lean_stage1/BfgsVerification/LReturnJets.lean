import BfgsVerification.LNormalizedReturn

noncomputable section
open scoped BigOperators
open Matrix
namespace BfgsVerification.LReturnJets

structure Jet where
  value : ℝ
  tangent : ℝ

def Models (f : ℝ → ℝ) (j : Jet) : Prop := f 0=j.value ∧ HasDerivAt f j.tangent 0

def constant (a : ℝ) : Jet := ⟨a,0⟩
def add (a b : Jet) : Jet := ⟨a.value+b.value,a.tangent+b.tangent⟩
def neg (a : Jet) : Jet := ⟨-a.value,-a.tangent⟩
def sub (a b : Jet) : Jet := add a (neg b)
def mul (a b : Jet) : Jet := ⟨a.value*b.value,a.tangent*b.value+a.value*b.tangent⟩
def inv (a : Jet) : Jet := ⟨a.value⁻¹,-a.tangent/(a.value*a.value)⟩
def div (a b : Jet) : Jet := mul a (inv b)

theorem models_constant (a : ℝ) : Models (fun _ => a) (constant a) :=
  ⟨rfl,hasDerivAt_const 0 a⟩

theorem Models.add {f g : ℝ → ℝ} {a b : Jet} (hf : Models f a) (hg : Models g b) :
    Models (fun t => f t+g t) (add a b) := ⟨by dsimp only; rw [hf.1,hg.1]; rfl,hf.2.add hg.2⟩
theorem Models.neg {f : ℝ → ℝ} {a : Jet} (hf : Models f a) :
    Models (fun t => -f t) (neg a) := ⟨by dsimp only; rw [hf.1]; rfl,hf.2.neg⟩
theorem Models.sub {f g : ℝ → ℝ} {a b : Jet} (hf : Models f a) (hg : Models g b) :
    Models (fun t => f t-g t) (sub a b) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Models.mul {f g : ℝ → ℝ} {a b : Jet} (hf : Models f a) (hg : Models g b) :
    Models (fun t => f t*g t) (mul a b) := by
  refine ⟨by dsimp only; rw [hf.1,hg.1]; rfl,?_⟩
  simpa only [hf.1,hg.1] using hf.2.mul hg.2

theorem Models.inv {f : ℝ → ℝ} {a : Jet} (hf : Models f a) (ha : a.value ≠ 0) :
    Models (fun t => (f t)⁻¹) (inv a) := by
  refine ⟨by dsimp only; rw [hf.1]; rfl,?_⟩
  simpa only [hf.1,pow_two] using hf.2.inv (hf.1.trans_ne ha)

theorem Models.div {f g : ℝ → ℝ} {a b : Jet} (hf : Models f a) (hg : Models g b)
    (hb : b.value ≠ 0) : Models (fun t => f t/g t) (div a b) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hb)

abbrev JetVec := Fin 2 → Jet
abbrev JetMat := Fin 2 → Fin 2 → Jet

def ModelsVec (f : ℝ → Vec 2) (j : JetVec) : Prop := ∀ i, Models (fun t => f t i) (j i)
def ModelsMat (f : ℝ → Mat 2) (j : JetMat) : Prop := ∀ i k, Models (fun t => f t i k) (j i k)
def vecConstant (v : Vec 2) : JetVec := fun i => constant (v i)
def matConstant (H : Mat 2) : JetMat := fun i k => constant (H i k)
def vecSub (u v : JetVec) : JetVec := fun i => sub (u i) (v i)
def vecScale (a : Jet) (v : JetVec) : JetVec := fun i => mul a (v i)
def matAdd (H K : JetMat) : JetMat := fun i j => add (H i j) (K i j)
def matSub (H K : JetMat) : JetMat := fun i j => sub (H i j) (K i j)
def matScale (a : Jet) (H : JetMat) : JetMat := fun i j => mul a (H i j)
def matMul (H K : JetMat) : JetMat := fun i j => add (mul (H i 0) (K 0 j)) (mul (H i 1) (K 1 j))
def mulVec (H : JetMat) (v : JetVec) : JetVec := fun i => add (mul (H i 0) (v 0)) (mul (H i 1) (v 1))
def dot (u v : JetVec) : Jet := add (mul (u 0) (v 0)) (mul (u 1) (v 1))
def outer (u v : JetVec) : JetMat := fun i j => mul (u i) (v j)

theorem models_vecConstant (v : Vec 2) : ModelsVec (fun _ => v) (vecConstant v) :=
  fun i => models_constant (v i)
theorem models_matConstant (H : Mat 2) : ModelsMat (fun _ => H) (matConstant H) :=
  fun i j => models_constant (H i j)

theorem ModelsVec.sub {f g : ℝ → Vec 2} {a b : JetVec} (hf : ModelsVec f a) (hg : ModelsVec g b) :
    ModelsVec (fun t => f t-g t) (vecSub a b) := fun i => (hf i).sub (hg i)
theorem ModelsVec.scale {f : ℝ → ℝ} {g : ℝ → Vec 2} {a : Jet} {b : JetVec}
    (hf : Models f a) (hg : ModelsVec g b) :
    ModelsVec (fun t => f t • g t) (vecScale a b) := fun i => hf.mul (hg i)
theorem ModelsMat.add {f g : ℝ → Mat 2} {a b : JetMat} (hf : ModelsMat f a) (hg : ModelsMat g b) :
    ModelsMat (fun t => f t+g t) (matAdd a b) := fun i j => (hf i j).add (hg i j)
theorem ModelsMat.sub {f g : ℝ → Mat 2} {a b : JetMat} (hf : ModelsMat f a) (hg : ModelsMat g b) :
    ModelsMat (fun t => f t-g t) (matSub a b) := fun i j => (hf i j).sub (hg i j)
theorem ModelsMat.scale {f : ℝ → ℝ} {g : ℝ → Mat 2} {a : Jet} {b : JetMat}
    (hf : Models f a) (hg : ModelsMat g b) :
    ModelsMat (fun t => f t • g t) (matScale a b) := fun i j => hf.mul (hg i j)
theorem ModelsMat.mul {f g : ℝ → Mat 2} {a b : JetMat} (hf : ModelsMat f a) (hg : ModelsMat g b) :
    ModelsMat (fun t => f t*g t) (matMul a b) := by
  intro i j
  simpa only [Matrix.mul_apply,Fin.sum_univ_two] using ((hf i 0).mul (hg 0 j)).add ((hf i 1).mul (hg 1 j))
theorem ModelsMat.mulVec {f : ℝ → Mat 2} {g : ℝ → Vec 2} {a : JetMat} {b : JetVec}
    (hf : ModelsMat f a) (hg : ModelsVec g b) :
    ModelsVec (fun t => (f t).mulVec (g t)) (mulVec a b) := by
  intro i
  simpa only [Matrix.mulVec,dotProduct,Fin.sum_univ_two] using ((hf i 0).mul (hg 0)).add ((hf i 1).mul (hg 1))
theorem ModelsVec.dot {f g : ℝ → Vec 2} {a b : JetVec} (hf : ModelsVec f a) (hg : ModelsVec g b) :
    Models (fun t => BfgsVerification.dot (f t) (g t)) (dot a b) := by
  simpa only [BfgsVerification.dot,Fin.sum_univ_two] using ((hf 0).mul (hg 0)).add ((hf 1).mul (hg 1))
theorem ModelsVec.outer {f g : ℝ → Vec 2} {a b : JetVec} (hf : ModelsVec f a) (hg : ModelsVec g b) :
    ModelsMat (fun t => BfgsVerification.outer (f t) (g t)) (outer a b) := fun i j => (hf i).mul (hg j)

def inverseUpdate (H : JetMat) (s y : JetVec) : JetMat :=
  let r := inv (dot y s)
  matAdd (matMul (matMul (matSub (matConstant 1) (matScale r (outer s y))) H)
    (matSub (matConstant 1) (matScale r (outer y s)))) (matScale r (outer s s))

theorem models_inverseUpdate {H : ℝ → Mat 2} {s y : ℝ → Vec 2} {jH : JetMat} {js jy : JetVec}
    (hH : ModelsMat H jH) (hs : ModelsVec s js) (hy : ModelsVec y jy)
    (ht : BfgsVerification.dot (y 0) (s 0) ≠ 0) :
    ModelsMat (fun t => inverseBFGS (H t) (s t) (y t)) (inverseUpdate jH js jy) := by
  have hr := (hy.dot hs).inv ((hy.dot hs).1.symm.trans_ne ht)
  exact (((models_matConstant 1).sub (ModelsMat.scale hr (hs.outer hy))).mul hH).mul
    ((models_matConstant 1).sub (ModelsMat.scale hr (hy.outer hs))) |>.add
      (ModelsMat.scale hr (hs.outer hs))

end BfgsVerification.LReturnJets
