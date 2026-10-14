# TODO: Manuscript review

Review date: 13 October 2026. Reviewer: AI assistant (Claude), at the author's request.

Scope: notation, typesetting and claim wording in the article (`paper/`). The seed
numerics were re-checked in the first reading and all matched. Unless an item says
otherwise, no mathematical statement and no Lean declaration changed.

**Status (13 October 2026):** M1 to M5 are resolved; M6 awaits an author decision.

## Resolved

- [x] **M1: Qualifier spacing in displays.** In `paper/sections/failure.tex`, the
  seed query bounds `|g_i^Tz|<3 (i=0,1,2)` and the local model condition
  `|g_i^Th|\le a_\ell/2 (i=0,1,2)` lost the space before the qualifier, so they
  rendered as `3(i=0,1,2)` and `a_\ell/2(i=0,1,2)`, which read as products. The
  same happened to `(g_i-g_k)^Tq (k\ne i)` in `paper/appendices/seed_certificate.tex`.
  All three now use `\quad`. A scan of every display in `paper/` found no other
  case. The seed appendix is shared, so `companion/appendices/seed_certificate.tex`
  was regenerated with `editorial/prepare_shared_appendix.py`.

- [x] **M2: `[z]_2` was undefined.** The 13 September exposition revision replaced
  `z_2` by `[z]_2` and removed the sentence saying that it is a coordinate. Lemma
  `art:seed_cycle` now reads "each such point $z$, with second coordinate
  $[z]_2$, satisfies".

- [x] **M3: Symbols reused for different objects in the same argument.**
  - `local.tex`, proof of Lemma `art:localization`: the sphere gap was `\omega`,
    which the article reserves for `1-c_2`. It is now `\delta`.
  - `lower_curvature.tex`: the return factor `r=(M_3)_{11}` is now `\hat\rho`
    (`r=1/128` is the scale ratio later in the same appendix; `\hat\rho(P_*)=\rho`).
    The matrix-shape coordinates `(b,e)` are now `(\zeta,\eta)`, since `b` is the
    scalar-family parameter `b_i`, `\psi_b`, `t_b` in the same appendix. The
    unspecified derivative blocks `C`, `\mu a`, `\mu b'` are now marked `*`.
  - `planar_geometry.tex`, proof of Lemma `art:planar-field`: the local
    branch-gradient Lipschitz constant `L` is now `M` (`L` is the lemma's transport
    constant). The endpoint gradient limits `a,b` and the limiting step direction
    `e` are now `\bar g,\bar h` and `\hat s` (`a,b,e` are the entries of `Dw`).
    The one-sided comparison is stated on `[0,1]` rather than `[a,b]`, and
    `a=\nabla f_i(x)`, `b=\nabla f_j(x)` are written out.
  - `energy.tex` (proof of Theorem `art:reciprocal-growth`) and `global.tex`
    (proof of Theorem `art:radial-equivalence`): the gradient bound `G` is now
    `\Lambda`, since `G` is the seed maximum.
  - `editorial/NOTATION_MAP.md` records the new article symbols and their
    companion counterparts.

- [x] **M4: Regularity-map table.** Table `art:regularity-map` used `\hline`; it
  now uses booktabs rules, like the article's other tables.

- [x] **M5: Abstract overstated what the planar example shows.** "an explicit
  curved-interface example requires moving comparison geometry beyond the radial
  criterion" is now "in an explicit curved-interface example, moving comparison
  geometry proves convergence although the radial criterion fails". Theorem
  `art:nonradial-example` shows that the radial criterion fails and the moving
  field succeeds; it does not show that every fixed comparison geometry fails.
  Of several equivalent wordings, this one keeps the abstract at 22 lines without
  breaking a line after "smooth–" or "curved-".

**Verification.** Both documents were rebuilt; page counts are unchanged (article
49, companion 108). The changed pages (article 1, 9, 12, 13, 16, 26, 30, 32, 38,
39, 42, 44, 45; companion PDF page 102, printed page 96) were inspected visually. LaTeX warnings are
unchanged, except that the underfull page warning on article page 32 (the table)
improved from badness 10000 to 4608. `editorial/CLAIM_LEDGER.json` and
`companion/PROOF_CORRESPONDENCE.html` were regenerated; only file hashes and line
positions changed. `python3 editorial/generate_companion.py --check` passes. The
PDFs under `release/` predate these edits.

## Open

- [ ] **M6: Theorem `art:local-failure-lower` fixes $c_1=10^{-4}$, $c_2=1/2$.**
  The upper-curvature Theorem `art:local-failure` and Proposition
  `art:quadratic_failure` cover every $0<c_1\le1/3$, $c_1<c_2<1$. Mathematically the
  local lower-curvature theorem should extend in the same way, and even uniformly:
  the seed's Armijo margins hold at $c_1=1/3$ and its weak-Wolfe margins hold for
  every $c_2>0$, so one stable-manifold orbit should serve every admissible pair,
  and the copying and whitening steps do not depend on the constants. The Lean
  targets do not cover this yet. `LActualCopies`/`LWhitening` and their non-strict
  versions in `bfgs_lean_article/BfgsArticle/LNonStrictLocal.lean` fix
  `1/10000` and `1/2` through the library's source run `LSeedCopies.run`. Closing
  this item needs a source run with margins at $1/3$ whose queries lie in
  `LEmbedding.localDomain`, new copy and whitening families in
  `bfgs_lean_article`, a new axiom audit, ledger additions, and statement edits
  in the article and companion. Awaiting author decision.
