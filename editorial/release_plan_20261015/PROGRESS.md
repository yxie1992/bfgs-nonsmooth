# Progress: release-run study (read-only)

Started 15 Oct 2026 04:41. Scratch: this directory.
- head/BFGS-non-smooth: `git archive` export of 1abfe07 (build.sh + checks run there)
- clone/BFGS-non-smooth: `git clone --no-hardlinks` of the repo at 1abfe07 (worktrees wt_* and
  symlinked .lake/.toolchain for read-only tests)
- tools/: scratch scripts (stmt_diff.py, tree_changes.py)

- [x] Read prompt, AGENTS.md, HANDOFF.md, release/README.md
- [x] Map release/ (RELEASE.json, SOURCE_MANIFEST.json, validation/, history/)
- [x] Read build.sh, package_release.py, validate_archive.py, verify_release_inputs.py,
      verify_historical_baseline.py, restore_git_history.py, cache_binding.py, check_documents.py,
      refresh_correspondence.py, render_review.py, assemble_claim_ledger.py, ledger_addenda.py,
      positive_formal/verify.py, legacy gate (verify_rigorous_master_report.py, verify_report_attributions.py)
- [x] Git history of the 13 Sep release: 3e8b5c6 freeze -> package -> validate -> fa54d6a -> push -> db4dc37
- [x] Read-only checks on HEAD (results below)
- [x] Write PLAN.md (done 15 Oct; snippets A.1 and A.5 tested in the scratch clone)
- [x] Clean-up: scratch ZIPs deleted; the clone's .lake/.toolchain symlinks to the September host
      removed (so nothing in scratch can write into it). Repository unchanged (61 modified files
      of the step-2 agents, no untracked files); $H unchanged (package indexes still dated Sept).
      head/ and clone/ (1.9 GB in all) can be deleted once the coordinator no longer needs them.

## Results of read-only checks (HEAD 1abfe07, scratch)

- build.sh in export: PASS, 5.3 s; paper 49 pp, companion 108 pp; no overfull, no undefined.
  Regenerated files equal to HEAD except editorial/logs/{paper,companion}_build.log, document_checks.json.
  Logs contain absolute paths (TEXINPUTS) -> always differ per checkout.
- verify_release_inputs.py in export (no .lake/.toolchain => source-only cache scope): FAIL on 3 checks
  "Reviewed source contracts" (positive: planar_geometry, energy, global, local; negative:
  negative_lower, failure, seed_certificate, lower_curvature; root: master, energy, verification,
  companion/chapters/13_L.tex). All 18 other checks PASS. 1.7 s.
- refresh_correspondence.py --check: FAIL at HEAD (first: 'Existing mathematical display changed'
  global.tex art:inward-to-radial). PASS at 3e8b5c6, db4dc37, c76e663. Stale since f8ca4cc (receipt bytes:
  pins assemble_claim_ledger.py hash), statement changes since 5476ba7 (art:quadratic_failure).
- Statement diff 3e8b5c6 -> HEAD (Sept normalizer): statements changed art:seed_cycle,
  art:local-failure-lower, art:lower_hyperbolic, art:quadratic_failure; displays changed
  art:inward-to-radial, art:lower_return. 31 statements, 55 labeled displays at HEAD.
- verify_historical_baseline.py (scratch clone): FAIL "Current history differs beyond added editorial
  Lean files; investigate explicitly" (79 added Lean-ish paths: 46 under bfgs_lean_article incl.
  lean-toolchain/lakefile.toml/lake-manifest.json). Frozen inputs PASS (761 inputs, 286 artifacts).
  With the filter extended to added files under bfgs_lean_article/: PASS in 13.5 s (legacy gate fails at
  HEAD at the expected assertion; passes at 00362c0).
- cache_binding.py --check, cache_binding_04 seal: PASS (8.9 s) with .lake/.toolchain -> old Sept host
  /Users/yxie/Documents/ChatGPT/BFGS-non-smooth/bfgs_lean_stage1 (8853 objects, 32470 files);
  FAIL "Project traces changed since the binding run" with .lake -> new repo's .lake (built 14 Oct;
  .olean bytes identical, trace logs differ: absolute toolchain path, LEAN_PATH via ../bfgs_lean_stage1).
- Old toolchain lean/lake binaries are byte-identical to ~/.elan ones (runs on macOS 26).
- check_coverage.py: plain exit 0; --strict exit 1 (open companion discrepancies); --strict
  --allow-discrepancies exit 0. 0.3 s.
- package_release safe_name: HEAD has no unsafe/reserved tracked paths; no symlinks; 7 executables.
- Tree: 4899 files, 920 MB (Sept: 4597, 771 MB); git bundle of HEAD 55.8 MB.

## Dry run in the scratch clone (no Lean)

- Scratch commit 8cdc06e in clone (freeze-style RELEASE.json, new PDFs, render manifest).
- package_release.py: PASS, 17 s, ZIP 154,641,216 bytes, 4904 members (4899 sources + 5).
- validate_archive.py patched copy (stop before the Lean supplements; focused check non-fatal),
  --lean-cache-root old host: 40 s; extraction + history restore OK; both PDFs rebuilt
  byte-identically (b168feb9 / aeddfa5a, path-independent), all 157 pages pixel-identical, text identical;
  companion preservation PASS; Sept focused check FAIL (expected); cache binding before/after PASS;
  temporary extraction removed.
- render_review.py (venv python): 19.6 s, adds render_history entry, status PENDING_VISUAL_REVIEW.
- Changed pages vs 13 Sep PDFs (text): article 22/49, companion 21/108 (100-108 shifted).
- tools/receipt_review.py reproduces the 13 Sep final_receipt_review.json numbers (39 cmds, 78 logs, 156 pp).

## Key facts

1. Sept releases ran on THIS Mac in /Users/yxie/Documents/ChatGPT/BFGS-non-smooth (still present at
   db4dc37 with .toolchain 1.5G, .lake 5.9G, .cache; and the git-ignored ZIPs of all four editions;
   13 Sep zip b76bd245 verified). Validation then took 2.3 min (39 commands, 141 s).
2. New repo dir name `bfgs-nonsmooth` -> archive root `bfgs-nonsmooth/` (was `BFGS-non-smooth/`).
3. Repo has bfgs_lean_stage1/.lake (new, unsealed) but no .toolchain -> in-repo verify_release_inputs
   cache check FAILS ("only partially available"). Use --lean-cache-root old host for validate_archive.
4. Symlinked .lake/.toolchain show as untracked (pattern `.lake/` does not match symlinks).
5. render_review.py needs Pillow: use ~/.venvs/pdf/bin/python (python3 lacks PIL).
6. Tools: TeX Live 2025/Homebrew pdfTeX 1.40.27, latexmk 4.86a, Node v22.22.0 (same as Sept), Poppler 26.04.
