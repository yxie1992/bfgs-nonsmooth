import BfgsVerification.HessianUpdate

/-!
# Lean coverage: `paper/appendices/matrix_algebra.tex`

Appendix `art:matrix-algebra` ("The BFGS compression calculation"): Lemma
`art:gram-compression` and its proof. Register:
`editorial/lean_coverage/register/A_matrix_algebra.json`.

## Standing assumptions

Every theorem below states the assumptions of Theorem `art:minor-hierarchy`
(`paper/sections/energy.tex:130-141`) explicitly, with these names:

* `hH : H.PosDef` is $H\succ0$ (real symmetric positive definite, `H : Mat n`);
* `hs : s = -α • (H *ᵥ g)` is $s=-\alpha Hg$, and `hα : 0 < α` is $\alpha>0$;
* `hq_def : q = dot g (H *ᵥ g)` and `hq : 0 < q` are $q=g^THg>0$;
* `hβ_def : β = -dot y (H *ᵥ g) / q` and `hβ : 0 < β` are $\beta=-y^THg/q>0$;
* `hHplus : Hplus = inverseBFGS H s y` says that $H_+$ is the inverse-BFGS update
  \eqref{art:update}. The library definition `inverseBFGS H s y` is literally
  `(1 - t⁻¹ • outer s y) * H * (1 - t⁻¹ • outer y s) + t⁻¹ • outer s s` with `t = dot y s`.

The lemma adds `Z : Matrix (Fin n) (Fin j) ℝ` with `hZ : Zᵀ * Z = 1` ($Z$ has $j$
orthonormal columns), `hj : 1 ≤ j` and `hjn : j ≤ n`. The objects that the proof
introduces are variables whose defining equations are hypotheses, with the TeX names:
`v`, `κ`, `P` (line 14), `F` for $\mathcal F$ (display 002), and `A`, `a`, `b`, `r`, `u`,
`w`, `z` (display 003). Each display is stated under all the assumptions above and the
definitions of the objects that it involves. A hypothesis whose name starts with `_` is
one of these assumptions that the Lean proof does not need.

## Notation

* `dot x z` is $x^Tz$, `M *ᵥ x` is $Mx$, `outer x z` is $xz^T$, `Mᵀ` is $M^T$, `1` is $I$;
* `metricGram H X` is $X^THX$; `fromCols X Y` is the block matrix $[X\ Y]$;
  `replicateCol Unit y` is the single column $y$; `(Matrix.of ![a, b])ᵀ` is $[a\ b]$, the
  matrix with columns $a,b$, so `Matrix.of ![a, b]` is $[a\ b]^T$;
* $\operatorname{Gram}_H(y,Z)=[y\ Z]^TH[y\ Z]$ (`energy.tex:150`) is
  `metricGram H (fromCols (replicateCol Unit y) Z)`. The proof also uses
  $\operatorname{Gram}_H(g,y,Z)=[g\ y\ Z]^TH[g\ y\ Z]$, which is
  `metricGram H (fromCols (Matrix.of ![g, y])ᵀ Z)`, and
  $\operatorname{Gram}_H(g,Z)=[g\ Z]^TH[g\ Z]$;
* `!![p, q; r, s]` is the $2\times2$ matrix with rows $(p,q)$ and $(r,s)$.

## Items

| Item | Lines | Lean |
|---|---|---|
| `lemma/art:gram-compression` (with `disp/001`) | 3-12 | `gram_compression` |
| `disp/002` | 16-19 | `update_split` |
| `disp/003` | 21-26 | `compression_posDef` |
| `disp/004` | 28-33 | `compression_formula` |
| `disp/005` (`art:compression-determinant`) | 36-40 | `compression_determinant` |
| `disp/006` | 42-46 | `gram_schur` |
| `disp/007` | 49-54 | `compression_gram_bound` |

The undisplayed steps of the proof are stated too: `kappa_eq_and_curvature` (lines 14-15),
`gram_dets_nonneg` (lines 47-48), `compression_update`, `compression_add_rank_one` and `u_bounds`
(lines 56-62), and `full_dimension_case` (lines 64-67). `gram_compression` is proved from these
theorems along the paper's proof. `det_update` proves the identity for $j=n$ again from the
library's `inverseBFGS_step_det_beta`. An `example` at the end shows that the standing
assumptions are satisfiable, so no statement here is vacuous.
-/

noncomputable section
open Matrix BfgsVerification

namespace BfgsCoverage.Article.MatrixAlgebra

/-! ### Helpers -/

/-- A positive definite real matrix is symmetric. -/
theorem isSymm_of_posDef {n : ℕ} {H : Mat n} (hH : H.PosDef) : H.IsSymm := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian.eq

/-- $x^THz=z^THx$ for symmetric $H$. -/
theorem dot_mulVec_comm {n : ℕ} {H : Mat n} (hH : H.IsSymm) (x z : Vec n) :
    dot x (H *ᵥ z) = dot z (H *ᵥ x) := by
  change x ⬝ᵥ (H *ᵥ z) = z ⬝ᵥ (H *ᵥ x)
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hH.eq, dotProduct_comm]

/-- Orthonormal columns are linearly independent. -/
theorem mulVec_injective_of_orthonormal {n j : ℕ} {Z : Matrix (Fin n) (Fin j) ℝ}
    (hZ : Zᵀ * Z = 1) : Function.Injective Z.mulVec := by
  apply Function.LeftInverse.injective (g := Zᵀ.mulVec)
  intro x
  rw [Matrix.mulVec_mulVec, hZ, Matrix.one_mulVec]

/-- The compression $Z^T\mathcal FZ$ in the library's form
`CompressionDeterminant.compression A a b κ r` $=A-\kappa^{-1}(ab^T+ba^T)+(r/\kappa^2)aa^T$. -/
theorem compression_eq_library {n j : ℕ} (H : Mat n) (g y : Vec n) (hH : H.PosDef)
    (Z : Matrix (Fin n) (Fin j) ℝ)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ)
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ)
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a b : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (hb : b = Zᵀ *ᵥ (H *ᵥ y)) (r : ℝ) (hr : r = dot y (H *ᵥ y)) :
    Zᵀ * F * Z = CompressionDeterminant.compression A a b κ r := by
  subst hF hP hv hA ha hb hr
  exact BFGSCompression.projected_compression H Z (H *ᵥ g) y κ (isSymm_of_posDef hH)

/-! ### The proof of Lemma `art:gram-compression`, in the order of the TeX -/

/-- Proof of Lemma `art:gram-compression`, undisplayed claims of
`paper/appendices/matrix_algebra.tex:14-15` (not a register item):
"Put $v=Hg$, $\kappa=g^THy=-\beta q$ \dots Since $y^Ts=\alpha\beta q$".

Under the assumptions of Theorem `art:minor-hierarchy`,
$g^THy=-\beta q$ and $y^Ts=\alpha\beta q$. -/
theorem kappa_eq_and_curvature {n : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (_hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y) :
    dot g (H *ᵥ y) = -β * q ∧ dot y s = α * β * q := by
  have hβq : β * q = -dot y (H *ᵥ g) := by
    rw [hβ_def]
    field_simp
  constructor
  · rw [dot_mulVec_comm (isSymm_of_posDef hH) g y]
    linarith
  · rw [hs, dot_smul_right, mul_assoc, hβq]
    ring

/-- Item `A/matrix_algebra/disp/002` (`paper/appendices/matrix_algebra.tex:16-19`), in the
proof of Lemma `art:gram-compression`.

Under the assumptions of Theorem `art:minor-hierarchy` (the display does not involve $Z$),
put $v=Hg$, $\kappa=g^THy$ and $P=I-vy^T/\kappa$. Then the update becomes
\[ H_+=\mathcal F+\frac{\alpha}{\beta q}vv^T, \qquad \mathcal F=PHP^T. \] -/
theorem update_split {n : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ) :
    Hplus = F + (α / (β * q)) • outer v v := by
  have hκβ : κ = -β * q := hκ.trans
    (kappa_eq_and_curvature H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus).1
  have hq' : metricEnergy H g = q := hq_def.symm
  have hβ' : -dot y (H *ᵥ g) / metricEnergy H g = β := by rw [hq']; exact hβ_def.symm
  have hform := inverseBFGS_projection_form H g y α hα.ne' (hq'.symm ▸ hq.ne')
    (hβ'.symm ▸ hβ.ne')
  dsimp only at hform
  rw [hβ', hq'] at hform
  subst hHplus hs hF hP hv
  change inverseBFGS H (bfgsStep H g α) y = _
  rw [hform, hκβ, neg_mul, inv_neg, neg_smul, sub_neg_eq_add, transpose_add, transpose_one,
    transpose_smul, BFGSCompression.transpose_outer]

/-- Item `A/matrix_algebra/disp/003` (`paper/appendices/matrix_algebra.tex:21-26`), in the
proof of Lemma `art:gram-compression`: the claim $A=Z^THZ\succ0$ of the display
\[ A=Z^THZ\succ0,\quad a=Z^THg,\quad b=Z^THy,\quad r=y^THy,\quad
   u=a^TA^{-1}a,\quad w=a^TA^{-1}b,\quad z=b^TA^{-1}b. \]
The other entries only define notation; the later theorems take $a,b,r,u,w,z$ as variables
with exactly these defining equations. -/
theorem compression_posDef {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (_hq_def : q = dot g (H *ᵥ g)) (_hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (A : Mat j) (hA : A = Zᵀ * H * Z) :
    A.PosDef := by
  subst hA
  exact metricGram_posDef hH (mulVec_injective_of_orthonormal hZ)

/-- Item `A/matrix_algebra/disp/004` (`paper/appendices/matrix_algebra.tex:28-33`), in the
proof of Lemma `art:gram-compression`.

Under the assumptions of the lemma, with $v,\kappa,P,\mathcal F$ and $A,a,b,r$ as defined
in the proof,
\[ Z^T\mathcal FZ =A-[a\ b]
   \begin{pmatrix}-r/\kappa^2&1/\kappa\\1/\kappa&0\end{pmatrix}[a\ b]^T. \] -/
theorem compression_formula {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (_hq_def : q = dot g (H *ᵥ g)) (_hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (_hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (_hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ)
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a b : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (hb : b = Zᵀ *ᵥ (H *ᵥ y)) (r : ℝ) (hr : r = dot y (H *ᵥ y)) :
    Zᵀ * F * Z =
      A - (Matrix.of ![a, b])ᵀ * !![-r / κ ^ 2, 1 / κ; 1 / κ, 0] * Matrix.of ![a, b] := by
  rw [compression_eq_library H g y hH Z v hv κ P hP F hF A hA a b ha hb r hr]
  ext i k
  simp [CompressionDeterminant.compression, outer, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Item `A/matrix_algebra/disp/005`, equation `art:compression-determinant`
(`paper/appendices/matrix_algebra.tex:36-40`), in the proof of Lemma `art:gram-compression`.

Under the assumptions of the lemma, with $v,\kappa,P,\mathcal F$ and $A,a,b,r,u,w,z$ as
defined in the proof,
\[ \det(Z^T\mathcal FZ) =\frac{\det A}{\kappa^2}\bigl((\kappa-w)^2+u(r-z)\bigr). \] -/
theorem compression_determinant {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ)
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a b : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (hb : b = Zᵀ *ᵥ (H *ᵥ y)) (r : ℝ) (hr : r = dot y (H *ᵥ y))
    (u w z : ℝ) (hu : u = dot a (A⁻¹ *ᵥ a)) (hw : w = dot a (A⁻¹ *ᵥ b))
    (hz : z = dot b (A⁻¹ *ᵥ b)) :
    (Zᵀ * F * Z).det = A.det / κ ^ 2 * ((κ - w) ^ 2 + u * (r - z)) := by
  have hκβ : κ = -β * q := hκ.trans
    (kappa_eq_and_curvature H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus).1
  have hκ0 : κ ≠ 0 := by
    rw [hκβ]
    exact mul_ne_zero (neg_ne_zero.mpr hβ.ne') hq.ne'
  have hApos : A.PosDef := hA ▸ metricGram_posDef hH (mulVec_injective_of_orthonormal hZ)
  have hdet := CompressionDeterminant.compression_det A a b κ r
    (isUnit_iff_ne_zero.mpr hApos.det_pos.ne') (isSymm_of_posDef hApos) hκ0
  subst hu hw hz
  rw [compression_eq_library H g y hH Z v hv κ P hP F hF A hA a b ha hb r hr,
    div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hκ0)]
  linear_combination hdet

/-- Item `A/matrix_algebra/disp/006` (`paper/appendices/matrix_algebra.tex:42-46`), in the
proof of Lemma `art:gram-compression`.

Under the assumptions of the lemma, with $\kappa$ and $A,a,b,r,u,w,z$ as defined in the
proof, Schur complements give
\[ \det\operatorname{Gram}_H(y,Z)=\det A(r-z),\qquad
   \det\operatorname{Gram}_H(g,y,Z)=\det A\bigl((q-u)(r-z)-(\kappa-w)^2\bigr). \] -/
theorem gram_schur {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (_hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (κ : ℝ) (hκ : κ = dot g (H *ᵥ y))
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a b : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (hb : b = Zᵀ *ᵥ (H *ᵥ y)) (r : ℝ) (hr : r = dot y (H *ᵥ y))
    (u w z : ℝ) (hu : u = dot a (A⁻¹ *ᵥ a)) (hw : w = dot a (A⁻¹ *ᵥ b))
    (hz : z = dot b (A⁻¹ *ᵥ b)) :
    (metricGram H (fromCols (replicateCol Unit y) Z)).det = A.det * (r - z) ∧
      (metricGram H (fromCols (Matrix.of ![g, y])ᵀ Z)).det =
        A.det * ((q - u) * (r - z) - (κ - w) ^ 2) := by
  have hZinj := mulVec_injective_of_orthonormal hZ
  have hcols : fromCols (Matrix.of ![g, y])ᵀ Z = fromCols (fun i k => ![g i, y i] k) Z := by
    ext i k
    rcases k with k | k
    · fin_cases k <;> rfl
    · rfl
  subst hq_def hκ hA ha hb hr hu hw hz
  exact ⟨metricGram_det_append_one hH y Z hZinj,
    hcols ▸ metricGram_det_append_two hH g y Z hZinj⟩

/-- Proof of Lemma `art:gram-compression`, undisplayed claim of
`paper/appendices/matrix_algebra.tex:47-48` (not a register item): "Both are Gram
determinants and hence nonnegative, including when their column families are dependent",
i.e. $\det\operatorname{Gram}_H(y,Z)\ge0$ and $\det\operatorname{Gram}_H(g,y,Z)\ge0$. -/
theorem gram_dets_nonneg {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (_hq_def : q = dot g (H *ᵥ g)) (_hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (_hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n) :
    0 ≤ (metricGram H (fromCols (replicateCol Unit y) Z)).det ∧
      0 ≤ (metricGram H (fromCols (Matrix.of ![g, y])ᵀ Z)).det :=
  ⟨metricGram_det_nonneg hH.posSemidef _, metricGram_det_nonneg hH.posSemidef _⟩

/-- Item `A/matrix_algebra/disp/007` (`paper/appendices/matrix_algebra.tex:49-54`), in the
proof of Lemma `art:gram-compression`.

Under the assumptions of the lemma, with $v,\kappa,P,\mathcal F$ as defined in the proof,
\[ \det(Z^T\mathcal FZ)
   =\frac{q\det\operatorname{Gram}_H(y,Z)-\det\operatorname{Gram}_H(g,y,Z)}{\beta^2q^2}
   \le\frac{\det\operatorname{Gram}_H(y,Z)}{\beta^2q}. \] -/
theorem compression_gram_bound {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (hj : 1 ≤ j) (hjn : j ≤ n)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ) :
    (Zᵀ * F * Z).det =
        (q * (metricGram H (fromCols (replicateCol Unit y) Z)).det -
          (metricGram H (fromCols (Matrix.of ![g, y])ᵀ Z)).det) / (β ^ 2 * q ^ 2) ∧
      (q * (metricGram H (fromCols (replicateCol Unit y) Z)).det -
          (metricGram H (fromCols (Matrix.of ![g, y])ᵀ Z)).det) / (β ^ 2 * q ^ 2) ≤
        (metricGram H (fromCols (replicateCol Unit y) Z)).det / (β ^ 2 * q) := by
  obtain ⟨A, hA⟩ : ∃ A : Mat j, A = Zᵀ * H * Z := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Vec j, a = Zᵀ *ᵥ (H *ᵥ g) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Vec j, b = Zᵀ *ᵥ (H *ᵥ y) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = dot y (H *ᵥ y) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = dot a (A⁻¹ *ᵥ a) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = dot a (A⁻¹ *ᵥ b) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = dot b (A⁻¹ *ᵥ b) := ⟨_, rfl⟩
  have hdet := compression_determinant H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn v hv κ hκ P hP F hF A hA a b ha hb r hr u w z hu hw hz
  obtain ⟨hy, hgy⟩ := gram_schur H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn κ hκ A hA a b ha hb r hr u w z hu hw hz
  have hnonneg := (gram_dets_nonneg H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn).2
  have hκβ : κ = -β * q := hκ.trans
    (kappa_eq_and_curvature H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus).1
  have hκ2 : κ ^ 2 = β ^ 2 * q ^ 2 := by rw [hκβ]; ring
  have hden : 0 < β ^ 2 * q ^ 2 := by positivity
  constructor
  · rw [hdet, hy, hgy, ← hκ2]
    field_simp
    ring
  · rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith [mul_nonneg hnonneg (by positivity : (0 : ℝ) ≤ β ^ 2 * q)]

/-- Proof of Lemma `art:gram-compression`, undisplayed step of
`paper/appendices/matrix_algebra.tex:56-59` (not a register item): by display 002 the
compression of the update is the compression of $\mathcal F$ plus $\rho aa^T$ with
$\rho=\alpha/(\beta q)$:
\[ Z^TH_+Z=Z^T\mathcal FZ+\frac{\alpha}{\beta q}aa^T. \] -/
theorem compression_update {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (_hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ)
    (a : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g)) :
    Zᵀ * Hplus * Z = Zᵀ * F * Z + (α / (β * q)) • outer a a := by
  rw [update_split H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus v hv κ hκ P hP F hF,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    BFGSCompression.congruence_outer, ha, hv]

/-- Proof of Lemma `art:gram-compression`, undisplayed claims of
`paper/appendices/matrix_algebra.tex:56-59` (not a register item): "Adding $\rho aa^T$ to
the compression changes the coefficient $r/\kappa^2$ by $\rho$. The same $2\times2$
expansion therefore changes its determinant by exactly $\rho\det A\,u$. No invertibility of
$Z^T\mathcal FZ$ is used." For every real $\rho$,
\[ Z^T\mathcal FZ+\rho aa^T=A-[a\ b]
   \begin{pmatrix}-(r/\kappa^2+\rho)&1/\kappa\\1/\kappa&0\end{pmatrix}[a\ b]^T,\qquad
   \det(Z^T\mathcal FZ+\rho aa^T)=\det(Z^T\mathcal FZ)+\rho\det A\,u. \] -/
theorem compression_add_rank_one {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (_hα : 0 < α)
    (_hq_def : q = dot g (H *ᵥ g)) (_hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (_hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (_hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ)
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a b : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (hb : b = Zᵀ *ᵥ (H *ᵥ y)) (r : ℝ) (hr : r = dot y (H *ᵥ y))
    (u : ℝ) (hu : u = dot a (A⁻¹ *ᵥ a)) (ρ : ℝ) :
    Zᵀ * F * Z + ρ • outer a a =
        A - (Matrix.of ![a, b])ᵀ * !![-(r / κ ^ 2 + ρ), 1 / κ; 1 / κ, 0] *
          Matrix.of ![a, b] ∧
      (Zᵀ * F * Z + ρ • outer a a).det = (Zᵀ * F * Z).det + ρ * A.det * u := by
  have hApos : A.PosDef := hA ▸ metricGram_posDef hH (mulVec_injective_of_orthonormal hZ)
  rw [compression_eq_library H g y hH Z v hv κ P hP F hF A hA a b ha hb r hr]
  constructor
  · ext i k
    simp [CompressionDeterminant.compression, outer, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [CompressionDeterminant.compression_add_rank_one_det A a b κ r ρ
      (isUnit_iff_ne_zero.mpr hApos.det_pos.ne') (isSymm_of_posDef hApos), hu]

/-- Proof of Lemma `art:gram-compression`, undisplayed claims of
`paper/appendices/matrix_algebra.tex:59-61` (not a register item): "For
$\rho=\alpha/(\beta q)$, the Schur complement of $A$ in $\operatorname{Gram}_H(g,Z)$ gives
$0\le u\le q$, so the increase is at most $(\alpha/\beta)\det A$." Stated as
\[ \det\operatorname{Gram}_H(g,Z)=\det A\,(q-u),\qquad 0\le u\le q,\qquad
   \frac{\alpha}{\beta q}\det A\,u\le\frac\alpha\beta\det A. \]
($u\ge0$ holds because $A^{-1}\succ0$; the Schur complement gives $u\le q$.) -/
theorem u_bounds {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (_hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (_hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (_hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (_hj : 1 ≤ j) (_hjn : j ≤ n)
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (u : ℝ) (hu : u = dot a (A⁻¹ *ᵥ a)) :
    (metricGram H (fromCols (replicateCol Unit g) Z)).det = A.det * (q - u) ∧
      0 ≤ u ∧ u ≤ q ∧ α / (β * q) * A.det * u ≤ α / β * A.det := by
  have hZinj := mulVec_injective_of_orthonormal hZ
  have hApos : A.PosDef := hA ▸ metricGram_posDef hH hZinj
  have hu0 : 0 ≤ u := by
    rw [hu]
    simpa [star_trivial] using hApos.inv.posSemidef.2 a
  have huq : u ≤ q := by
    subst hA ha hu hq_def
    exact compressed_energy_le hH g Z hZinj
  refine ⟨?_, hu0, huq, CompressionAlgebra.rank_one_increment_upper_bound α β q A.det u hα.le
    hβ hq hApos.det_pos.le huq⟩
  subst hA ha hu hq_def
  exact metricGram_det_append_one hH g Z hZinj

/-- Proof of Lemma `art:gram-compression`, undisplayed claims of
`paper/appendices/matrix_algebra.tex:64-67` (not a register item): "When $j=n$, $Z$ is an
orthogonal basis and $u=q$, $w=\kappa$, $z=r$. Equation~\eqref{art:compression-determinant}
then vanishes, while the rank-one increase is exactly $(\alpha/\beta)\det A$. Orthogonal
invariance gives the stated determinant identity." Stated as: if $j=n$, then $ZZ^T=I$,
$u=q$, $w=\kappa$, $z=r$, $\det(Z^T\mathcal FZ)=0$,
$\frac{\alpha}{\beta q}\det A\,u=\frac\alpha\beta\det A$,
$\det(Z^TH_+Z)=\frac\alpha\beta\det A$ and $\det H_+=\frac\alpha\beta\det H$. -/
theorem full_dimension_case {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (hj : 1 ≤ j) (hjn : j ≤ n)
    (v : Vec n) (hv : v = H *ᵥ g) (κ : ℝ) (hκ : κ = dot g (H *ᵥ y))
    (P : Mat n) (hP : P = 1 - κ⁻¹ • outer v y) (F : Mat n) (hF : F = P * H * Pᵀ)
    (A : Mat j) (hA : A = Zᵀ * H * Z) (a b : Vec j) (ha : a = Zᵀ *ᵥ (H *ᵥ g))
    (hb : b = Zᵀ *ᵥ (H *ᵥ y)) (r : ℝ) (hr : r = dot y (H *ᵥ y))
    (u w z : ℝ) (hu : u = dot a (A⁻¹ *ᵥ a)) (hw : w = dot a (A⁻¹ *ᵥ b))
    (hz : z = dot b (A⁻¹ *ᵥ b)) (htop : j = n) :
    Z * Zᵀ = 1 ∧ (u = q ∧ w = κ ∧ z = r) ∧ (Zᵀ * F * Z).det = 0 ∧
      α / (β * q) * A.det * u = α / β * A.det ∧
      (Zᵀ * Hplus * Z).det = α / β * A.det ∧ Hplus.det = α / β * H.det := by
  have hD := compression_determinant H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn v hv κ hκ P hP F hF A hA a b ha hb r hr u w z hu hw hz
  have hupd := compression_update H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn v hv κ hκ P hP F hF a ha
  have hinc := (compression_add_rank_one H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn v hv κ hκ P hP F hF A hA a b ha hb r hr u hu (α / (β * q))).2
  subst htop
  have hZZ : Z * Zᵀ = 1 := Matrix.mul_eq_one_comm.mp hZ
  have hHunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hH.det_pos.ne'
  have hAinv : A⁻¹ = Zᵀ * H⁻¹ * Z := by
    rw [hA]
    apply Matrix.inv_eq_right_inv
    calc Zᵀ * H * Z * (Zᵀ * H⁻¹ * Z) = Zᵀ * (H * ((Z * Zᵀ) * (H⁻¹ * Z))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hZZ, Matrix.one_mul, ← Matrix.mul_assoc H, Matrix.mul_nonsing_inv H hHunit,
            Matrix.one_mul, hZ]
  have hsolve : ∀ x : Vec _, A⁻¹ *ᵥ (Zᵀ *ᵥ (H *ᵥ x)) = Zᵀ *ᵥ x := by
    intro x
    have hM : A⁻¹ * Zᵀ * H = Zᵀ := by
      rw [hAinv]
      calc Zᵀ * H⁻¹ * Z * Zᵀ * H = Zᵀ * (H⁻¹ * ((Z * Zᵀ) * H)) := by
            simp only [Matrix.mul_assoc]
        _ = Zᵀ := by rw [hZZ, Matrix.one_mul, Matrix.nonsing_inv_mul H hHunit, Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  have horth : ∀ p x : Vec _, dot (Zᵀ *ᵥ p) (Zᵀ *ᵥ x) = dot p x := by
    intro p x
    change (Zᵀ *ᵥ p) ⬝ᵥ (Zᵀ *ᵥ x) = p ⬝ᵥ x
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hZZ, one_mulVec]
  have huq : u = q := by
    rw [hu, ha, hsolve, horth, hq_def]
    exact dotProduct_comm _ _
  have hwκ : w = κ := by
    rw [hw, ha, hb, hsolve, horth, hκ, dot_mulVec_comm (isSymm_of_posDef hH) g y]
    exact dotProduct_comm _ _
  have hzr : z = r := by
    rw [hz, hb, hsolve, horth, hr]
    exact dotProduct_comm _ _
  have hD0 : (Zᵀ * F * Z).det = 0 := by
    rw [hD, hwκ, hzr]
    ring
  have hρ : α / (β * q) * A.det * u = α / β * A.det := by
    rw [huq]
    field_simp
    ring
  have hcomp : (Zᵀ * Hplus * Z).det = α / β * A.det := by
    rw [hupd, hinc, hD0, hρ, zero_add]
  have hinv (M : Mat _) : (Zᵀ * M * Z).det = M.det := by
    have h1 : Zᵀ.det * Z.det = 1 := by rw [← Matrix.det_mul, hZ, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul]
    linear_combination M.det * h1
  refine ⟨hZZ, ⟨huq, hwκ, hzr⟩, hD0, hρ, hcomp, ?_⟩
  rw [← hinv Hplus, hcomp, hA, hinv H]

/-- The identity $\det H_+=(\alpha/\beta)\det H$ of Lemma `art:gram-compression`
(`paper/appendices/matrix_algebra.tex:11`) and Theorem `art:minor-hierarchy`
(`paper/sections/energy.tex:140`), under the assumptions of Theorem `art:minor-hierarchy`,
derived from the library theorem `inverseBFGS_step_det_beta` (a second proof, independent
of `full_dimension_case`). -/
theorem det_update {n : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y) :
    Hplus.det = α / β * H.det := by
  have hg : g ≠ 0 := by
    rintro rfl
    rw [hq_def] at hq
    simp [dot] at hq
  have ht : 0 < dot y (bfgsStep H g α) := by
    have h := (kappa_eq_and_curvature H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ
      hHplus).2
    rw [hs] at h
    change dot y (bfgsStep H g α) = α * β * q at h
    rw [h]
    positivity
  have hq' : metricEnergy H g = q := hq_def.symm
  have hβ' : -dot y (H *ᵥ g) / metricEnergy H g = β := by rw [hq']; exact hβ_def.symm
  have h := inverseBFGS_step_det_beta hH hg y hα ht
  rw [hβ'] at h
  subst hHplus hs
  exact h

/-! ### Lemma `art:gram-compression` -/

/-- Item `A/matrix_algebra/lemma/art:gram-compression`, Lemma `art:gram-compression`
(`paper/appendices/matrix_algebra.tex:3-12`), including its display
`A/matrix_algebra/disp/001` (lines 6-10).

Under the assumptions of Theorem~\ref{art:minor-hierarchy}, let $Z$ have $j$ orthonormal
columns, $1\le j\le n$. Then
\[ \det(Z^TH_+Z)\le\frac{\det\operatorname{Gram}_H(y,Z)}{\beta^2q}
   +\frac\alpha\beta\det(Z^THZ). \]
For $j=n$, $\det H_+=(\alpha/\beta)\det H$.

The proof is the paper's: `compression_update`, `compression_add_rank_one`,
`compression_gram_bound` and `u_bounds` give the inequality, `full_dimension_case` the case $j=n$.
The library proves the inequality for every `Z` with independent columns as
`BFGSCompression.compressed_inverseBFGS_bound`, and the identity as
`inverseBFGS_step_det_beta` (see `det_update`). -/
theorem gram_compression {n j : ℕ} (H Hplus : Mat n) (g y s : Vec n) (α q β : ℝ)
    (hH : H.PosDef) (hs : s = -α • (H *ᵥ g)) (hα : 0 < α)
    (hq_def : q = dot g (H *ᵥ g)) (hq : 0 < q)
    (hβ_def : β = -dot y (H *ᵥ g) / q) (hβ : 0 < β)
    (hHplus : Hplus = inverseBFGS H s y)
    (Z : Matrix (Fin n) (Fin j) ℝ) (hZ : Zᵀ * Z = 1) (hj : 1 ≤ j) (hjn : j ≤ n) :
    (Zᵀ * Hplus * Z).det ≤
        (metricGram H (fromCols (replicateCol Unit y) Z)).det / (β ^ 2 * q) +
          α / β * (Zᵀ * H * Z).det ∧
      (j = n → Hplus.det = α / β * H.det) := by
  obtain ⟨v, hv⟩ : ∃ v : Vec n, v = H *ᵥ g := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = dot g (H *ᵥ y) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Mat n, P = 1 - κ⁻¹ • outer v y := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Mat n, F = P * H * Pᵀ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Mat j, A = Zᵀ * H * Z := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Vec j, a = Zᵀ *ᵥ (H *ᵥ g) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Vec j, b = Zᵀ *ᵥ (H *ᵥ y) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = dot y (H *ᵥ y) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = dot a (A⁻¹ *ᵥ a) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = dot a (A⁻¹ *ᵥ b) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = dot b (A⁻¹ *ᵥ b) := ⟨_, rfl⟩
  refine ⟨?_, fun htop => (full_dimension_case H Hplus g y s α q β hH hs hα hq_def hq hβ_def
    hβ hHplus Z hZ hj hjn v hv κ hκ P hP F hF A hA a b ha hb r hr u w z hu hw hz
    htop).2.2.2.2.2⟩
  have hupd := compression_update H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn v hv κ hκ P hP F hF a ha
  have hinc := (compression_add_rank_one H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn v hv κ hκ P hP F hF A hA a b ha hb r hr u hu (α / (β * q))).2
  obtain ⟨hid, hle⟩ := compression_gram_bound H Hplus g y s α q β hH hs hα hq_def hq hβ_def
    hβ hHplus Z hZ hj hjn v hv κ hκ P hP F hF
  have hincr := (u_bounds H Hplus g y s α q β hH hs hα hq_def hq hβ_def hβ hHplus
    Z hZ hj hjn A hA a ha u hu).2.2.2
  rw [← hid] at hle
  rw [hupd, hinc, ← hA]
  linarith

/-! ### Non-vacuity -/

/-- The standing assumptions of this file can all hold at once: $n=j=1$, $H=Z=I$, $g=1$,
$y=-1$, $\alpha=1$, so that $s=-1$, $q=1$ and $\beta=1$. -/
example : ∃ (H Hplus : Mat 1) (g y s : Vec 1) (α q β : ℝ) (Z : Matrix (Fin 1) (Fin 1) ℝ),
    H.PosDef ∧ s = -α • (H *ᵥ g) ∧ 0 < α ∧ q = dot g (H *ᵥ g) ∧ 0 < q ∧
      β = -dot y (H *ᵥ g) / q ∧ 0 < β ∧ Hplus = inverseBFGS H s y ∧
      Zᵀ * Z = 1 ∧ 1 ≤ 1 ∧ 1 ≤ 1 := by
  refine ⟨1, _, ![1], ![-1], _, 1, 1, 1, 1, Matrix.PosDef.one, rfl, one_pos, ?_, one_pos, ?_,
    one_pos, rfl, by simp, le_rfl, le_rfl⟩
  · simp [dot]
  · simp [dot]

end BfgsCoverage.Article.MatrixAlgebra
