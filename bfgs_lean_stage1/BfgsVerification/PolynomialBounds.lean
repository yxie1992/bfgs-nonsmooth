import BfgsVerification.Definitions

noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BfgsVerification.PolynomialBounds

def monomial (w : List (Fin 2)) (x : Vec 2) : ℝ := (w.map x).prod

@[simp] theorem monomial_nil (x : Vec 2) : monomial [] x = 1 := rfl
@[simp] theorem monomial_cons (i : Fin 2) (w : List (Fin 2)) (x : Vec 2) :
    monomial (i::w) x = x i * monomial w x := rfl

theorem monomial_abs_le_one (w : List (Fin 2)) {x : Vec 2} (hx : ∀ i, |x i| ≤ 1) :
    |monomial w x| ≤ 1 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [monomial_cons, abs_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (hx i) ih (abs_nonneg _) (by norm_num)
      _ = 1 := by ring

theorem monomial_abs_le_radius {w : List (Fin 2)} (hw : w ≠ [])
    {x : Vec 2} {r : ℝ} (hr : r ≤ 1) (hx : ∀ i, |x i| ≤ r) :
    |monomial w x| ≤ r := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons i w =>
    rw [monomial_cons,abs_mul]
    calc
      _ ≤ r*1 := mul_le_mul (hx i) (monomial_abs_le_one w (fun j => (hx j).trans hr))
        (abs_nonneg _) ((abs_nonneg _).trans (hx i))
      _ = r := mul_one r

theorem monomial_abs_sub_le (w : List (Fin 2)) {x y : Vec 2}
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) :
    |monomial w x-monomial w y| ≤ w.length * ‖x-y‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hd : |x i-y i| ≤ ‖x-y‖ := by simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (x-y) i
    have he : monomial (i::w) x-monomial (i::w) y =
        (x i-y i)*monomial w x+y i*(monomial w x-monomial w y) := by simp only [monomial_cons]; ring
    rw [he]
    calc
      _ ≤ |x i-y i| * |monomial w x|+|y i| * |monomial w x-monomial w y| := by
        simpa only [abs_mul] using abs_add_le ((x i-y i)*monomial w x) (y i*(monomial w x-monomial w y))
      _ ≤ ‖x-y‖*1+1*(w.length*‖x-y‖) := add_le_add
        (mul_le_mul hd (monomial_abs_le_one w hx) (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul (hy i) ih (abs_nonneg _) (by norm_num))
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem monomial_quadratic_abs_sub_le {w : List (Fin 2)} (hw : 2 ≤ w.length)
    {x y : Vec 2} {r : ℝ} (hr : r ≤ 1)
    (hx : ∀ i, |x i| ≤ r) (hy : ∀ i, |y i| ≤ r) :
    |monomial w x-monomial w y| ≤ w.length * r * ‖x-y‖ := by
  cases w with
  | nil => simp at hw
  | cons i w =>
    have hn : w ≠ [] := by intro h; simp [h] at hw
    have hr0 : 0 ≤ r := (abs_nonneg _).trans (hx i)
    have hd : |x i-y i| ≤ ‖x-y‖ := by simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (x-y) i
    have he : monomial (i::w) x-monomial (i::w) y =
        (x i-y i)*monomial w x+y i*(monomial w x-monomial w y) := by simp only [monomial_cons]; ring
    rw [he]
    calc
      _ ≤ |x i-y i| * |monomial w x|+|y i| * |monomial w x-monomial w y| := by
        simpa only [abs_mul] using abs_add_le ((x i-y i)*monomial w x) (y i*(monomial w x-monomial w y))
      _ ≤ ‖x-y‖*r+r*(w.length*‖x-y‖) := add_le_add
        (mul_le_mul hd (monomial_abs_le_radius hn hr hx) (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul (hy i) (monomial_abs_sub_le w (fun j => (hx j).trans hr) (fun j => (hy j).trans hr))
          (abs_nonneg _) hr0)
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem polynomial_quadratic_abs_sub_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (w : ι → List (Fin 2)) (hw : ∀ i, 2 ≤ (w i).length)
    {x y : Vec 2} {r : ℝ} (hr : r ≤ 1)
    (hx : ∀ i, |x i| ≤ r) (hy : ∀ i, |y i| ≤ r) :
    |(∑ i, a i*monomial (w i) x)-(∑ i, a i*monomial (w i) y)| ≤
      (∑ i, |a i| *(w i).length)*r*‖x-y‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |a i*monomial (w i) x-a i*monomial (w i) y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| *((w i).length*r*‖x-y‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (monomial_quadratic_abs_sub_le (hw i) hr hx hy) (abs_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

end BfgsVerification.PolynomialBounds
