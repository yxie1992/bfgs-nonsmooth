import BfgsVerification.PlanarTransportAlgebra
import BfgsVerification.ConvexSubdifferential
import BfgsVerification.CertificateGeometry

/-! Supporting-normal separation underlying C's disjoint corner normal sets.
No smoothness, curvature bound, or angle chart is assumed in these lemmas. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter Matrix
namespace BfgsVerification
namespace PlanarNormalGeometry

def SupportsSetAt {n : ℕ} (K : Set (Vec n)) (p a : Vec n) : Prop :=
  p ∈ K ∧ a ≠ 0 ∧ ∀ z ∈ K, dot a (z-p) ≤ 0

/-- A nonzero supporting normal puts a point on the actual frontier. -/
theorem mem_frontier_of_support {n : ℕ} {K : Set (Vec n)} (hK : IsClosed K)
    {p a : Vec n} (hp : SupportsSetAt K p a) : p ∈ frontier K := by
  rw [hK.frontier_eq]
  refine ⟨hp.1,?_⟩
  intro hi
  have hnhds : K ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hi
  have hc : Continuous (fun t : ℝ => p+t • a) := by fun_prop
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), p+t • a ∈ K := by
    have ht : Tendsto (fun t : ℝ => p+t • a) (𝓝[>] 0) (𝓝 p) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ht.eventually hnhds
  obtain ⟨t,htK,ht⟩ := (he.and self_mem_nhdsWithin).exists
  have hs := hp.2.2 (p+t • a) htK
  have heq : dot a (p+t • a-p) = t*sqNorm a := by
    rw [add_sub_cancel_left]
    change dotProduct a (t • a) = _
    rw [dotProduct_smul]
    simpa only [smul_eq_mul] using congrArg (fun u : ℝ => t*u) (CertificateGeometry.dot_self a)
  rw [heq] at hs
  have hpos : 0 < sqNorm a := by
    apply lt_of_le_of_ne (sqNorm_nonneg a)
    intro hz
    exact hp.2.1 ((CertificateGeometry.sqNorm_eq_zero_iff a).mp hz.symm)
  exact (not_lt_of_ge hs) (mul_pos ht hpos)

/-- A common normal at two points supports the entire joining segment. -/
theorem segment_support_of_common_normal {n : ℕ} {K : Set (Vec n)} (hK : Convex ℝ K)
    {p z a : Vec n} (hp : SupportsSetAt K p a) (hz : SupportsSetAt K z a) :
    ∀ w ∈ segment ℝ p z, SupportsSetAt K w a := by
  have hzp : dot a (z-p) = 0 := by
    have h1 := hp.2.2 z hz.1
    have h2 := hz.2.2 p hp.1
    have hn : dot a (p-z) = -dot a (z-p) := by
      change dotProduct a (p-z) = -dotProduct a (z-p)
      rw [show p-z=-(z-p) by abel,dotProduct_neg]
    rw [hn] at h2
    linarith
  intro w hw
  have hwK := hK.segment_subset hp.1 hz.1 hw
  obtain ⟨r,t,hr,ht,hrt,rfl⟩ := hw
  have hd : dot a ((r • p+t • z)-p)=0 := by
    have he : r • p+t • z-p=t • (z-p) := by
      have he : r=1-t := by linarith
      rw [he]
      module
    rw [he]
    change dotProduct a (t • (z-p))=0
    rw [dotProduct_smul]
    change t*dot a (z-p)=0
    rw [hzp,mul_zero]
  refine ⟨hwK,hp.2.1,?_⟩
  intro y hy
  have he : y-(r • p+t • z)=(y-p)-((r • p+t • z)-p) := by abel
  rw [he]
  change dotProduct a ((y-p)-((r • p+t • z)-p))≤0
  rw [dotProduct_sub]
  change dot a (y-p)-dot a ((r • p+t • z)-p)≤0
  rw [hd,sub_zero]
  exact hp.2.2 y hy

/-- Strict contours forbid shared nonzero normals at distinct contour points.
This is the actual set-geometric separation used before choosing angular cutoffs. -/
theorem points_equal_of_common_normal {n : ℕ} {K : Set (Vec n)}
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (hstrict : ∀ p z : Vec n, segment ℝ p z ⊆ frontier K → p=z)
    {p z a : Vec n} (hp : SupportsSetAt K p a) (hz : SupportsSetAt K z a) : p=z := by
  apply hstrict p z
  intro w hw
  exact mem_frontier_of_support hKclosed (segment_support_of_common_normal hKconvex hp hz w hw)

/-- Every nonzero conic combination of the two actual supports is a supporting
normal of the current sublevel. Common positive pairing certifies nonzeroness. -/
theorem supportsSetAt_of_two_supports {n : ℕ} {F : Vec n → ℝ}
    {p a b v : Vec n} (ha : Homogeneous.Supports F p a) (hb : Homogeneous.Supports F p b)
    (hva : dot a v=1) (hvb : dot b v=1) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hrt : 0 < r+t) :
    SupportsSetAt {z | F z≤F p} p (r • a+t • b) := by
  change F p ≤ F p ∧ (r • a+t • b) ≠ 0 ∧ _
  refine ⟨le_rfl,?_,?_⟩
  · intro he
    have hp : dot (r • a+t • b) v = r+t := by
      change dotProduct (r • a+t • b) v = _
      rw [add_dotProduct,smul_dotProduct,smul_dotProduct]
      change r*dot a v+t*dot b v=r+t
      rw [hva,hvb]
      ring
    rw [he] at hp
    simp [dot] at hp
    linarith
  · intro z hz
    have h1 : dot a (z-p)≤0 := (ha z).trans (sub_nonpos.mpr hz)
    have h2 : dot b (z-p)≤0 := (hb z).trans (sub_nonpos.mpr hz)
    change dotProduct (r • a+t • b) (z-p)≤0
    rw [add_dotProduct,smul_dotProduct,smul_dotProduct]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr h1) (mul_nonpos_of_nonneg_of_nonpos ht h2)

end PlanarNormalGeometry
end BfgsVerification
