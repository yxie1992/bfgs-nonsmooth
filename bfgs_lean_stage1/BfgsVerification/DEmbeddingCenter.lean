import BfgsVerification.DEmbeddingRun
import BfgsVerification.DEmbeddingLocalization

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric

def descentDirection : Vec 2 := ![-1,16]

theorem seed_descent_ray {t : ℝ} (ht : 0 ≤ t) :
    SeedOrbit.objective seedC seedD (t • descentDirection)= -t := by
  have hb := root_tight_box
  have hg : -seedC+16*seedD < -1 := by
    dsimp [seedC, seedD]
    linarith [hb.1.1, hb.2.2]
  apply le_antisymm
  · unfold SeedOrbit.objective MaxAffine.Family.objective
    apply Finset.sup'_le
    intro i _
    change dot (SeedOrbit.gradient seedC seedD i) (t • descentDirection)+0 ≤ -t
    fin_cases i <;> norm_num [SeedOrbit.gradient, descentDirection, dot, g0, g1, g2, Fin.sum_univ_two]
    · ring_nf
      exact le_refl _
    · nlinarith [mul_le_mul_of_nonneg_left hg.le ht]
  · have he := (family seedC seedD).branch_le 0 (t • descentDirection)
    simpa [MaxAffine.Family.branch, family, SeedOrbit.gradient, descentDirection, dot, g0, Fin.sum_univ_two] using he

theorem center_directional_derivative (n : ℕ) :
    Tendsto (fun t : ℝ => (objective (center n+t • descentDirection)-objective (center n))/t)
      (𝓝[>] 0) (𝓝 (-((scale n)^2))) := by
  have hsmall (i : Fin 3) : ∀ᶠ t : ℝ in 𝓝 0,
      |dot (SeedOrbit.gradient seedC seedD i) (t • descentDirection)| < scale n/2 := by
    have hc : Continuous (fun t : ℝ => |t*dot (SeedOrbit.gradient seedC seedD i) descentDirection|) :=
      (continuous_id.mul continuous_const).abs
    have hz : |(0 : ℝ)*dot (SeedOrbit.gradient seedC seedD i) descentDirection| < scale n/2 := by
      simpa using half_pos (scale_pos n)
    simpa only [dot_smul_right] using (isOpen_lt hc continuous_const).mem_nhds hz
  have hall : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i : Fin 3,
      |dot (SeedOrbit.gradient seedC seedD i) (t • descentDirection)| < scale n/2 :=
    (Filter.eventually_all.mpr hsmall).filter_mono nhdsWithin_le_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [hall, self_mem_nhdsWithin] with t hsmall ht
  rw [local_cone n (fun i => (hsmall i).le), center_value, seed_descent_ray ht.le]
  have ht0 : t≠0 := ne_of_gt ht
  field_simp [ht0]

theorem initial_values_tendsto :
    Tendsto (fun n => objective (SeedEmbedding.point (center n) ((scale n)^2) 0)) atTop (𝓝 0) := by
  have he := (convex_continuous objective_convex).continuousAt.tendsto.comp initial_points_tendsto
  simpa only [objective_zero] using he

end BfgsVerification.DEmbedding
