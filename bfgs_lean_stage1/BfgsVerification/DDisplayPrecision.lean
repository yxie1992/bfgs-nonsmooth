import BfgsVerification.DDisplayActual

noncomputable section
namespace BfgsVerification.DDisplayPrecision
open IntervalBounds SeedOrbit
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem box_of_original_ball {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) :
    Bounds (318481427627118630646451312501/10^30) (x 0)
      (318481427627118630646451312504/10^30) ∧
    Bounds (-1025232119675748725481350870015/10^30) (x 1)
      (-1025232119675748725481350870012/10^30) := by
  have hc : |x 0-AlgebraicSeed.center 0|≤AlgebraicSeed.radius :=
    (show |x 0-AlgebraicSeed.center 0|≤‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 0).trans hx
  have hd : |x 1-AlgebraicSeed.center 1|≤AlgebraicSeed.radius :=
    (show |x 1-AlgebraicSeed.center 1|≤‖x-AlgebraicSeed.center‖ from
      norm_le_pi_norm (x-AlgebraicSeed.center) 1).trans hx
  obtain ⟨hc0,hc1⟩ := abs_le.mp hc
  obtain ⟨hd0,hd1⟩ := abs_le.mp hd
  norm_num [AlgebraicSeed.center,AlgebraicSeed.radius] at hc0 hc1 hd0 hd1
  unfold Bounds
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

def original : Fin 33 → ℝ :=
  ![(60199206107543764815373666287/1000000000000000000000000000000 : ℝ),
    (888432624149/1000000000000 : ℝ),
    (-41148698843/500000000000 : ℝ),
    (-111567375851/1000000000000 : ℝ),
    (-41148698843/500000000000 : ℝ),
    (12456061649/1000000000000 : ℝ),
    (-33336198843/500000000000 : ℝ),
    (26741469327/500000000000 : ℝ),
    (-2477119003/500000000000 : ℝ),
    (121854550561/1000000000000 : ℝ),
    (384526374149/1000000000000 : ℝ),
    (136479499149/1000000000000 : ℝ),
    (723217079/10000000000 : ℝ),
    (16722152343/25000000000 : ℝ),
    (68134215537/200000000000 : ℝ),
    (176563569667/1000000000000 : ℝ),
    (47254907829/500000000000 : ℝ),
    (26741469327/500000000000 : ℝ),
    (888432624149/1000000000000 : ℝ),
    (121854550561/1000000000000 : ℝ),
    (723217079/10000000000 : ℝ),
    (191644518397/250000000000 : ℝ),
    (-1 : ℝ),
    (196595468547/500000000000 : ℝ),
    (-46595789523/250000000000 : ℝ),
    (93801490893/250000000000 : ℝ),
    (-408559835243/500000000000 : ℝ),
    (468627450981/1000000000000 : ℝ),
    (122709386489/125000000000 : ℝ),
    (3456112132353/250000000000 : ℝ),
    (48595528663/50000000000 : ℝ),
    (317882559279/500000000000 : ℝ),
    (30228443081843/62500000000 : ℝ)]

def corrected : Fin 33 → ℝ :=
  ![(60199206107543764815373666287/1000000000000000000000000000000 : ℝ),
    (888432624149/1000000000000 : ℝ),
    (-41148698843/500000000000 : ℝ),
    (-111567375851/1000000000000 : ℝ),
    (-41148698843/500000000000 : ℝ),
    (12456061649/1000000000000 : ℝ),
    (-33336198843/500000000000 : ℝ),
    (26741469327/500000000000 : ℝ),
    (-990847601/200000000000 : ℝ),
    (121854550561/1000000000000 : ℝ),
    (384526374149/1000000000000 : ℝ),
    (136479499149/1000000000000 : ℝ),
    (723217079/10000000000 : ℝ),
    (16722152343/25000000000 : ℝ),
    (68134215537/200000000000 : ℝ),
    (176563569667/1000000000000 : ℝ),
    (47254907829/500000000000 : ℝ),
    (26741469327/500000000000 : ℝ),
    (888432624149/1000000000000 : ℝ),
    (121854550561/1000000000000 : ℝ),
    (723217079/10000000000 : ℝ),
    (191644518397/250000000000 : ℝ),
    (-1 : ℝ),
    (196595468547/500000000000 : ℝ),
    (-46595789523/250000000000 : ℝ),
    (375205963573/1000000000000 : ℝ),
    (-163423934097/200000000000 : ℝ),
    (23431372549/50000000000 : ℝ),
    (122709386489/125000000000 : ℝ),
    (3456112132353/250000000000 : ℝ),
    (48595528663/50000000000 : ℝ),
    (635765118557/1000000000000 : ℝ),
    (30228443081843/62500000000 : ℝ)]

/-- One unit in the last displayed decimal place. Rho has thirty, the tables twelve. -/
def unit (i : Fin 33) : ℝ := if i=0 then 1/10^30 else 1/10^12

/-- Five positions where the printed approximation is not nearest rounding. -/
def changed : Finset (Fin 33) := Finset.univ.filter
  (fun i : Fin 33 => i.val=8 ∨ i.val=25 ∨ i.val=26 ∨ i.val=27 ∨ i.val=31)

theorem raw_bounds_on_original_ball {x : Vec 2}
    (hx : ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius) (i : Fin 33) :
    Bounds (DDisplayRaw.lower i) (DDisplayRaw.values (x 0) (x 1) i) (DDisplayRaw.upper i) := by
  obtain ⟨hc,hd⟩ := box_of_original_ball hx
  apply DDisplayRaw.values_bounds _ _ i
  · convert hc using 1 <;> norm_num
  · convert hd using 1 <;> norm_num

theorem actual_bounds (i : Fin 33) :
    Bounds (DDisplayRaw.lower i) (DDisplayActual.values i) (DDisplayRaw.upper i) := by
  rw [DDisplayActual.values_eq_raw]
  exact raw_bounds_on_original_ball AlgebraicSeed.root_spec.1 i

theorem corrected_interval (i : Fin 33) :
    corrected i-unit i/2 < DDisplayRaw.lower i ∧
      DDisplayRaw.upper i < corrected i+unit i/2 := by
  fin_cases i <;> norm_num [corrected,unit,DDisplayRaw.lower,DDisplayRaw.upper]

theorem original_interval (i : Fin 33) :
    original i-unit i < DDisplayRaw.lower i ∧
      DDisplayRaw.upper i < original i+unit i := by
  fin_cases i <;> norm_num [original,unit,DDisplayRaw.lower,DDisplayRaw.upper]

theorem corrected_error (i : Fin 33) :
    |DDisplayActual.values i-corrected i|<unit i/2 := by
  have h := actual_bounds i
  have he := corrected_interval i
  rw [abs_lt]
  constructor <;> linarith only [h.1,h.2,he.1,he.2]

theorem original_error (i : Fin 33) :
    |DDisplayActual.values i-original i|<unit i := by
  have h := actual_bounds i
  have he := original_interval i
  rw [abs_lt]
  constructor <;> linarith only [h.1,h.2,he.1,he.2]

theorem rounding_intervals (i : Fin 33) :
    if i ∈ changed then
      unit i/2 < DDisplayRaw.lower i-original i ∨
        unit i/2 < original i-DDisplayRaw.upper i
    else original i-unit i/2 < DDisplayRaw.lower i ∧
      DDisplayRaw.upper i < original i+unit i/2 := by
  fin_cases i <;> norm_num [changed,unit,original,DDisplayRaw.lower,DDisplayRaw.upper]

theorem rounding_classification (i : Fin 33) :
    if i ∈ changed then unit i/2 < |DDisplayActual.values i-original i|
    else |DDisplayActual.values i-original i|<unit i/2 := by
  have h := actual_bounds i
  have hr := rounding_intervals i
  by_cases hi : i ∈ changed
  · simp only [hi,if_true] at hr ⊢
    rcases hr with hr|hr
    · have ha := le_abs_self (DDisplayActual.values i-original i)
      linarith only [h.1,hr,ha]
    · have ha := neg_le_abs (DDisplayActual.values i-original i)
      linarith only [h.2,hr,ha]
  · simp only [hi,if_false] at hr ⊢
    rw [abs_lt]
    constructor <;> linarith only [h.1,h.2,hr.1,hr.2]

/-- Actual full-BFGS/objective quantities, every printed value, and exact rounding scope. -/
def PrintedPrecisionTarget : Prop :=
  (∀x : Vec 2, ‖x-AlgebraicSeed.center‖≤AlgebraicSeed.radius → ∀i : Fin 33,
    Bounds (DDisplayRaw.lower i) (DDisplayRaw.values (x 0) (x 1) i) (DDisplayRaw.upper i)) ∧
  (∀i : Fin 33, Bounds (DDisplayRaw.lower i) (DDisplayActual.values i) (DDisplayRaw.upper i)) ∧
  (∀i : Fin 33, |DDisplayActual.values i-original i|<unit i) ∧
  (∀i : Fin 33, |DDisplayActual.values i-corrected i|<unit i/2) ∧
  (∀i : Fin 33, if i ∈ changed then unit i/2 < |DDisplayActual.values i-original i|
    else |DDisplayActual.values i-original i|<unit i/2) ∧
  (∀j : Fin 3, HasFDerivAt (SeedOrbit.objective seedC seedD)
    (gradientFunctional (SeedOrbit.gradient seedC seedD j)) (point seedC seedD seedRatio j)) ∧
  (∀q : Fin 9, HasFDerivAt (SeedOrbit.objective seedC seedD)
    (gradientFunctional (SeedOrbit.gradient seedC seedD (trialActive q)))
      (trial seedC seedD seedRatio (trialPhase q) (trialLength q)))

theorem printedPrecision : PrintedPrecisionTarget :=
  ⟨fun _ hx => raw_bounds_on_original_ball hx,actual_bounds,original_error,
    corrected_error,rounding_classification,source_base_hasGradient,source_trial_hasGradient⟩

end BfgsVerification.DDisplayPrecision
