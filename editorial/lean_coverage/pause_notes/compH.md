> Pause note of the `compH` coverage agent (companion 07_H), written on 14 October
> 2026 on the Linux machine and moved here for the handoff (see `HANDOFF.md`).
> Paths are repository-relative. Scratch files under `/tmp/opencode/compH/` did not
> survive; the note contains the sources of the scripts that matter. Ledger hints:
> `python3 editorial/lean_coverage/companion_hints.py` writes
> `editorial/lean_coverage/hints/<stem>.json`.

# compH — Chapter 7 (07_H.tex) coverage: pause note (14 Oct 2026)

Agent: companion coverage agent for `companion/chapters/07_H.tex` (733 lines).
Register `editorial/lean_coverage/register/C_07_H.json`; module
`bfgs_lean_article/BfgsArticle/Coverage/Companion/Ch07H.lean`, namespace
`BfgsCoverage.Companion.Ch07H`. Scratch dir `/tmp/opencode/compH/`.

## State on disk

- **No repository file modified yet.** Register C_07_H.json untouched (43 mechanical items,
  all `status: null`). Module Ch07H.lean NOT created yet. No Lean process was run.
- Only scratch file: `/tmp/opencode/compH/hint_sigs.txt` (signatures of every ledger-hinted
  library name). Regenerate if /tmp was wiped (hints file is made by
  `editorial/lean_coverage/companion_hints.py` → `editorial/lean_coverage/hints/07_H.json`):
  ```
  cd bfgs-nonsmooth && python3 -c "
  import json
  d=json.load(open('bfgs_lean_stage1/master_report/DECLARATION_INDEX.json'))
  h=json.load(open('editorial/lean_coverage/hints/07_H.json'))
  names=sorted({n for r in h for n in (r.get('lean') or [])})
  for n in names:
      e=d.get(n); print('###',n,'|',e and e.get('module')); print(e and e.get('signature'))
  " > /tmp/opencode/compH/hint_sigs.txt
  ```

## Done (reading phase)

Read: AGENT_BRIEFS.md (lessons + companion brief), README.md, model MatrixAlgebra.lean +
A_matrix_algebra.json, Global.lean (homogeneous part, absRun/asymRun/oneDimRun,
`homogeneous_value_dichotomy` = A/global/prose/041, `maxLinear_convex_homogeneous`,
`sphere_minimum`, `coercive_homogeneous_positive`, `iterates_of_values`), Energy.lean header +
`admissible_iff`, `run_notation`, `update_formula`, `armijo_weak_wolfe`, `notation_display`,
`run_invariants`; 07_H.tex in full; 01_I.tex run convention (lines 25-57, 275-291);
02_M.tex Theorem `M:average` (lines 121-142: bounded gradients + fixed weak Wolfe + d_k→0 ⇒
geometric and arithmetic means of q_k⁻¹ → ∞; = article Theorem art:reciprocal-growth,
Energy.lean `reciprocal_growth`, library `reciprocalGrowth`/`ReciprocalGrowthTarget`);
check_coverage.py (docstring ``Item `id` (`companion/chapters/07_H.tex:a-b`)`` must match
register lines exactly; heading items have lines [L, L]).

Library files read: Definitions.lean (FullBFGSRun: H g α + posdef, energy_pos,
curvature_pos, update; q, d, beta), ObjectiveDefinitions.lean (AdmissibleBFGSRun has field
`convex`), ObjectiveRun.lean (`fullBFGS_positive_invariants H g α c₂ hH0 hg hα hc₂ hwolfe
hupd k` needs NO convexity → use for Lemma 7.3), Homogeneous.lean (PositiveDegreeOne,
Supports, supporting_euler, supporting_linear_le, supports_at_zero, global_supporting_bound,
homogeneous_new_pairing (h_k = d_k − Δ_k), *_nonneg/_nonpos, referenceCorrection_le_drop,
homogeneous_energy_identity, `homogeneousPotential k = referenceEnergy 0 k + ((1-c₁)/c₁) F(x_k)`,
homogeneous_potential_step), ObjectiveEnergy.lean (hessian, displacement, gradientChange,
curvature, referenceEnergy/Pairing/Correction, hessian_update), HomogeneousAffineGeometry.lean
(`recurrentValues g = {v | ∃ᶠ k in atTop, g k = v}`, eventually_mem_recurrentValues,
common_component_of_zero_not_mem_affineSpan, finite_range_sqNorm_bound),
HomogeneousAffineObstruction.lean (FullBFGSRun.common_component_energy_step = disp/026,
common_component_tail_sum_le, common_component_incompatible,
`FullBFGSRun.zero_mem_recurrent_affineSpan hfinite c hc hbeta hd` = Lemma 7.3 core,
maxLinear_recurrent_affine_zero, maxLinear_escape_of_zero_not_mem_affineSpan,
maxLinear_common_component_escape), ReportCoreTargets (HomogeneousDichotomyTarget),
ReportGeometryTargets (RecurrentAffineHullTarget, MaxLinearAffineEscapeTarget).

NOT yet read (needed): HomogeneousMaxLinear.lean (def `finiteMaxLinear A hA`,
maxLinear_value_dichotomy, gradient_mem/range_finite), HomogeneousCommonTilt.lean
(`commonTilt B hB`, last component one), ReportApplicationsTargets.lean:67
(PlanarHomogeneousEscapeTarget), AffineProjection.lean / AffineFiberProjection.lean (lift,
compress, fiberPoint, FullRowRank), HomogeneousRelativeInterior*.lean (RelativeInteriorZero),
HomogeneousCardinality.lean, SeedRecurrentRank.lean + where the seed three-piece admissible
run lives (grep SeedOrbit / AlgebraicSeedInfiniteOrbit; article Failure.lean/Verification.lean
may already expose it), HomogeneousPlanar*.lean, HomogeneousBlock*.lean, HomogeneousLowRank*.lean,
TwoPiece*.lean. All names + signatures are in hint_sigs.txt.

## Decisions taken

- Imports: library modules + `BfgsArticle.Coverage.Article.Global` and `.Energy` (allowed);
  reuse absRun (|x|, nonvacuity of 7.A/7.B), asymRun, oneDimRun, maxLinear_convex_homogeneous.
- Max-linear objective written in the article's shared form `(a : Fin m → Vec n) (hm : 0 < m)
  (hF_def : ∀ x, IsGreatest (Set.range fun i => dot (a i) x) (F x))`, converted to
  `Homogeneous.finiteMaxLinear (Finset.univ.image a) _` by a helper (to write).
- Section 7.5 (lines 241-365, ends "proving Theorem 7.A. □") = proof of Theorem 7.A: displays
  disp/013–disp/024 are LEAN items under standing assumptions (F convex, PositiveDegreeOne,
  R : AdmissibleBFGSRun n F, plus introduced objects as variables with defining equations);
  add a prose PROOF item for the proof; separate prose items for standalone remarks
  (dimension zero, line 258; "bounded-gradient assumption in M:average is automatic", 260-261;
  history 319-321 NON_CLAIM; formal-proof paragraph 367 NON_CLAIM + its mathematics LEAN).
- heading/001 Theorem 7.A: `∀ R, F(x_k)→0 ∨ F(x_k)→-∞` (hF convex as `_hF`), disp/002 PART_OF.
  Prose 62-66: bounded below ⇒ min f = 0 = f(0) and f_k→0; coercive ⇒ 0 unique minimizer and
  x_k→0; ∃k f(x_k)≤0 ⇒ f_k→-∞; finite-value branch ⇒ ∀k f(x_k)>0. Lines 58-60 ("no
  assumption ... bounded", "no finite gradient alphabet") → SAME_AS heading/001 + note.
- heading/002 Theorem 7.B = main claim (disp/003) AND the escape (disp/004), both PART_OF
  (line 438 "This proves Theorem 7.B" follows the escape argument). disp/005 commonTilt →
  DEFINITION + unfolding theorem; sentence 98-99 → LEAN (commonTilt_value_escape); 99-100
  "not a proof of finite termination" → NON_CLAIM. Non-vacuity of disp/004: in dimension ≤ 2
  no infinite run exists with 0 ∉ aff{a_i} (two-piece reduction; library
  TwoPieceBudget.no_infinite_linear_image) — note as exception, as Global did.
- heading/003 Theorem 7.C: Xor' (x_k→0 ∧ f_k→0 ∧ StrictAnti f_k) (f_k→-∞ ∧ Euclidean
  ‖x_k‖→∞); disp/006, disp/007 PART_OF. "limit nonstationary" → LEAN ¬(∀x, F 0 ≤ F x).
  "previously constructed exact three-piece example attains that alternative" → LEAN via the
  seed run (to locate); also gives non-vacuity of 7.C.
- heading/004 Lemma 7.3: stated WITHOUT convexity on explicit sequences x H g α, F arbitrary,
  0<c₁<c₂<1, (H 0).PosDef, α>0, g≠0, `_hgrad` HasFDerivAt (unused), step, update, Armijo,
  weak Wolfe, (Set.range g).Finite, ∃L ∀k L ≤ F(x k) ⇒ 0 ∈ affineSpan ℝ (recurrentValues g).
  Proof: build FullBFGSRun via fullBFGS_positive_invariants, then
  FullBFGSRun.zero_mem_recurrent_affineSpan (c = 1-c₂, beta_ge_of_weakWolfe, d→0 from Armijo).
  disp/025 (v with vᵀg=1), disp/026 (energy step) under the proof's standing assumptions.
- Open question lines 142-146 → OPEN `def ... : Prop` (finite max-linear, recurrent span
  finrank ≥ 3, f_k→0 (noncompact) ⇒ x_k converges), no proof.

## Discrepancy candidates (undecided)

1. Equation cross-references use the old numbering: "(2.1)" lines 284, 421 → tag (7.2.1);
   "(5.2)" line 341 → (7.5.2); "(7.3)" lines 577, 599 → (7.7.3); "(7.1)" line 655 → (7.7.1);
   "(7.2)" line 714 → (7.7.2). Probably a `typo` DISCREPANCY on one prose item (or note only).
2. Line 574-575 "Every accepted gradient transition is therefore linearly independent in the
   plane": true on the f_k→0 branch (standing "Assume f_k→0", line 543; library
   maxLinear_planar_transition_independent assumes all values > 0). Literal reading may fail:
   slopes a, 2a, transition 2a→a from f(x_k)>0 to f(x_{k+1})≤0 passes weak Wolfe iff c₂ ≥ 1/2
   and Armijo if c₁ ≤ 1/2 (single step). Decide: LEAN with note on standing assumption vs
   imprecision with a counterexample (would need a step inside an infinite run).
3. Everything else checked so far is true (disp/010, 014 (needs max_sphere f ≥ 0 for g=0),
   016-024, 031-036 block bounds, 466-469 cardinality r+1, 705 metric projection).

## Remaining (all of the production work)

1. Read the not-yet-read library files above; locate the seed three-piece run.
2. Write Ch07H.lean: header docstring (standing assumptions, notation, item table,
   non-vacuity), helpers, all coverage theorems in TeX order, OPEN def, examples
   (absRun for 7.A/7.B; seed run for 7.C; Lemma 7.3 hypotheses; 2-D run with nonzero limit for
   line 657 if feasible). Check with
   `export PATH="$HOME/.elan/bin:$PATH"; cd bfgs_lean_article && LEAN_NUM_THREADS=4 lake env lean BfgsArticle/Coverage/Companion/Ch07H.lean`
   (one Lean process at a time; no lake build/update/clean; no warnings allowed).
3. Fill C_07_H.json: 43 items + prose items `C/07_H/prose/<nnn>` (anchor, lines), PROOF items,
   NON_CLAIM reasons (line 23-24 XW history, 41 proof status, 319-321, 367, 726-733 literature,
   126-127 directions not asserted, 148-151 scope), discrepancies.
4. `python3 editorial/lean_coverage/check_coverage.py --strict --allow-discrepancies companion/chapters/07_H.tex` → exit 0.
5. Final answer per brief (counts by status, declarations ↔ items, discrepancies, items not
   covered, substantial proofs, check times, notes for other agents). Do not commit.
