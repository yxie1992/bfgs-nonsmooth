import BfgsVerification.DEmbeddingLocal
import BfgsVerification.SeedEmbeddingOracle

noncomputable section
open scoped Topology
open Set Filter Matrix
namespace BfgsVerification.DEmbedding
open SeedCycle SeedOrbit DScalarGeometric

theorem scale_le_sixteenth {n : ℕ} (hn : 1 ≤ n) : scale n ≤ 1/16 := by
  simpa [scale, theta] using scale_antitone hn

theorem certified_plateau {n : ℕ} (hn : 1 ≤ n) {z : Vec 2} {i : Fin 3}
    (hz : PointCertificate seedC seedD z i) (j : Fin 3) :
    |dot (SeedOrbit.gradient seedC seedD j) ((scale n)^2 • z)| < scale n/2 := by
  rw [dot_smul_right, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hs := scale_pos n
  have hu := scale_le_sixteenth hn
  have hprod := mul_lt_mul_of_pos_left (hz.branch_bounds j) (sq_pos_of_pos hs)
  nlinarith [mul_le_mul_of_nonneg_left hu hs.le]

theorem certified_value {n : ℕ} (hn : 1 ≤ n) {z : Vec 2} {i : Fin 3}
    (hz : PointCertificate seedC seedD z i) :
    objective (center n+(scale n)^2 • z)=(scale n)^3+((scale n)^2)^2*SeedOrbit.objective seedC seedD z := by
  rw [local_cone n (fun j => (certified_plateau hn hz j).le)]
  rw [objective_scale_at_active hz.active (sq_pos_of_pos (scale_pos n))]
  ring

theorem certified_hasGradient {n : ℕ} (hn : 1 ≤ n) {z : Vec 2} {i : Fin 3}
    (hz : PointCertificate seedC seedD z i) :
    HasFDerivAt objective (gradientFunctional ((scale n)^2 • SeedOrbit.gradient seedC seedD i))
      (center n+(scale n)^2 • z) :=
  objective_hasGradient_plateau (certified_plateau hn hz)
    (hz.active.scale (sq_pos_of_pos (scale_pos n)))

theorem orbit_certificate (k : ℕ) :
    PointCertificate seedC seedD (orbitPoint k) (phase k) :=
  (source_base_certificate (phase k)).scale (orbitScale_pos k) (orbitScale_le_one k)

def actualData {n : ℕ} (hn : 1 ≤ n) :
    SeedEmbedding.Data objective (center n) ((scale n)^2) ((scale n)^3) where
  convex := objective_convex
  values k := certified_value hn (orbit_certificate k)
  derivatives k := certified_hasGradient hn (orbit_certificate k)

def actualOracleData {n : ℕ} (hn : 1 ≤ n) :
    SeedEmbedding.OracleData objective (center n) ((scale n)^2) ((scale n)^3) where
  toData := actualData hn
  trial_values k q hq := certified_value hn (orbit_trial_point_certificate k q hq)
  trial_derivatives k q hq := certified_hasGradient hn (orbit_trial_point_certificate k q hq)

end BfgsVerification.DEmbedding
