# Handoff: resuming on another machine (14 October 2026)

Written by the coordinating agent (Claude in OpenCode) on the author's Linux
machine, at the author's request, to continue on the author's MacBook with
OpenCode and the same model. Standing instructions: `AGENTS.md`.

## State at the handoff

Everything is committed and pushed. Nothing is running and nothing was mid-edit.

| Work | State | Details |
|---|---|---|
| Lean review, passes 1–4 | done | `TODO_LEAN_REVIEW.md`, `bfgs_lean_article/README.md` |
| Manuscript review | M1–M6 fixed on 13 October; M7–M11, found by the Lean coverage, stay open until step 2 | `TODO_MANUSCRIPT_REVIEW.md` |
| Lean coverage, article | complete: all 616 items classified; 15 coverage modules, each reviewed by an independent agent, imported and audited | `TODO_LEAN_COVERAGE.md` |
| Lean coverage, companion | wave 1 (six groups) paused after reading and planning, with pause notes; waves 2 and 3 not started | `TODO_LEAN_COVERAGE.md`, `editorial/lean_coverage/` |

Latest checks:

- Axiom audit of commit `a2028c9` on a clean tree: PASS. 3862 declarations (every
  ledger, coverage-register and package name) use only `propext`,
  `Classical.choice` and `Quot.sound` (`bfgs_lean_article/AXIOM_AUDIT.json`).
- Kernel replay of `023f555` with lean4checker v4.19.0: PASS, 749 modules
  (`bfgs_lean_article/KERNEL_REPLAY.json`). It predates the coverage modules;
  rerun it at the end of the companion phase.
- `lake build` in `bfgs_lean_article` succeeds with no warnings from the coverage
  modules; `check_coverage.py` exits 0 (also with `--strict --allow-discrepancies`
  on the article files); `generate_companion.py --check` passes.

## Setting up the Mac

1. Tools:
   - Command line tools: `xcode-select --install` (git, clang).
   - Homebrew, then `brew install python@3.12 gh`. The scripts need Python 3.11 or
     newer, and macOS's own `python3` is older: call `python3.12`, or put
     Homebrew's Python first in `PATH`.
   - elan:
     `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none`.
     The `lean-toolchain` files select Lean 4.19.0.
   - TeX, for the PDFs: MacTeX (`brew install --cask mactex-no-gui`, includes
     `latexmk`), or TinyTeX plus `tlmgr install` for whatever a build reports
     missing.
   - PDF inspection: `python3.12 -m venv ~/.venvs/pdf && ~/.venvs/pdf/bin/pip install pymupdf`.
2. Clone, and log in to GitHub for pushing (`gh auth login`, or existing
   credentials):

       git clone https://github.com/yxie1992/bfgs-nonsmooth.git
       cd bfgs-nonsmooth

   If git has no credential helper, push with
   `git -c credential.helper='!gh auth git-credential' push origin main`.
3. Build the Lean code (about 7 GB of disk):

       export PATH="$HOME/.elan/bin:$PATH"
       cd bfgs_lean_stage1 && lake exe cache get    # Mathlib and its cache, about 5.6 GB
       cd ../bfgs_lean_article && lake build        # main library (736 modules) and article package

   On the Linux machine (24 cores, 15 GB RAM) the main library took 12 minutes
   with `LEAN_NUM_THREADS=10` and peaked near 10 GB of memory; with less memory,
   set `LEAN_NUM_THREADS` lower. Never run `lake update`.
4. Check the setup, from the repository root:

       python3.12 editorial/lean_coverage/check_coverage.py   # exit 0; companion items unclassified
       python3.12 editorial/generate_companion.py --check

   and build both PDFs once (commands in `AGENTS.md`).
5. Open the repository root as the OpenCode workspace, so that `AGENTS.md` is
   loaded. A first message such as "Read HANDOFF.md, check the setup, then resume
   the companion coverage" is enough. Your own OpenCode configuration (global
   instructions, plugins such as DCP for context pruning) is not part of this
   repository; set it up on the Mac as usual.

The agent briefs put scratch files under `/tmp/opencode/<tag>/`; if OpenCode on
the Mac names another scratch directory, use that one.

## Resuming the companion coverage

1. Write the ledger hints: `python3.12 editorial/lean_coverage/companion_hints.py`.
2. **Wave 1.** Start one fresh coverage agent per group: compM, compR, compC,
   compH, compD, compL (the Linux sessions cannot move). Each new agent reads its
   group's pause note, `editorial/lean_coverage/pause_notes/<group>.md`, which
   holds the earlier agent's reading, item plan and tentative decisions, and
   continues from there. The prompt is the header template under "Companion
   groups" in `editorial/lean_coverage/AGENT_BRIEFS.md`, filled with the clone's
   absolute path, the group's files, its hints and the pause-note sentence. Run as
   many at once as memory allows: in the article phase six agents ran at once on
   the 15 GB Linux machine. On the Mac, start with three or four and add more while
   memory pressure stays low.
3. **Per group**, when its coverage agent finishes:
   1. an independent reviewer agent ("Reviewer agent" brief);
   2. a fix pass by the coverage agent, continuing its session with the findings;
   3. the coordinator's check: `check_coverage.py --strict --allow-discrepancies
      <the group's TeX files>` exits 0, the module compiles, and every discrepancy
      is judged; accepted ones go to `TODO_MANUSCRIPT_REVIEW.md` (next number M12);
   4. add `import BfgsArticle.Coverage.Companion.<Name>` to
      `bfgs_lean_article/BfgsArticle.lean`; while no agent runs Lean,
      `lake build BfgsArticle.Coverage.Companion.<Name>`, then
      `lake build BfgsArticle` (no warnings from coverage files);
   5. commit ("Lean coverage of companion chapter … (independently reviewed)")
      and push.
4. **Wave 2:** compTA, compG, compFQ, compU (no pause notes). **Wave 3:**
   compFront, after all chapters, since it maps onto chapter items.
5. **End of the companion phase**, on a clean, committed tree. Each report records
   the commit and tree state at its start, so write the reports outside the
   repository and copy them in afterwards. Lower `--jobs` with less memory.

       cd bfgs_lean_article && lake build
       mkdir -p /tmp/opencode
       LEAN_NUM_THREADS=10 python3.12 scripts/axiom_audit.py --jobs 6 --write-guard --report /tmp/opencode/AXIOM_AUDIT.json
       git clone https://github.com/leanprover/lean4checker /tmp/opencode/lean4checker
       (cd /tmp/opencode/lean4checker && git checkout v4.19.0 && lake build)
       python3.12 scripts/kernel_replay.py --checker-repo /tmp/opencode/lean4checker --self-test --jobs 8 --report /tmp/opencode/KERNEL_REPLAY.json
       cp /tmp/opencode/AXIOM_AUDIT.json /tmp/opencode/KERNEL_REPLAY.json .

   `BfgsArticleAxioms.lean` should stay unchanged (182 pinned declarations).
   Commit the reports, update `TODO_LEAN_COVERAGE.md`, `TODO_LEAN_REVIEW.md` and
   `bfgs_lean_article/README.md`, and push.

## Findings in the pause notes (tentative)

- compD (`12_D.tex`, companion seed appendix): M11 does not recur in Chapter D,
  which fixes c₁ = 10⁻⁴, c₂ = 1/2. Planned discrepancies: trial-table decimals
  without value enclosures (line 190), and `Table~\ref{comp:trial_table}`
  pointing at a section label (line 186). Theorem `D:main` needs its own theorem;
  the appendix's closing sentence is correct.
- compM (`02_M.tex`): possible parallels of M10 (line 194, "∑R_k = o(∑q_k⁻¹)
  excludes a positive gap"; "O(N²) cumulative correction suffices"; line 211,
  "contradicting Theorem M:average"); G and V_η are undefined in
  `M:superquadratic`.
- compH (`07_H.tex`): in-text equation references use an old numbering; the
  linear independence at lines 574–575 may fail literally; an OPEN proposition for
  lines 142–146.
- compL (`13_L.tex`): M8 recurs at line 3; line 413 ("uses the fixed line-search
  pair") may be stale after the 13 October change to uniform constants.
- compC (`09_C.tex`): the cutoffs at lines 201–202 need the range (0, 1);
  `C:lem:steps` uses compactness implicitly.
- compR (`04_R.tex`): no recurrence of M7 so far; C_{η/2} ≥ 0 and sin θ ≠ 0 are
  probably notes.
- M8 also recurs at `01_I.tex:103` and `research_story.tex:52` (wave 3).

## After the Lean coverage

- **Step 2:** the line-by-line reading of the article's proofs, and the manuscript
  corrections (M7–M11 and the companion's discrepancies). After each TeX edit,
  build the PDF and inspect the changed pages. Then run `check_coverage.py`, which
  reports every item whose source changed ("source changed since
  classification"): re-check those Lean statements, then update the items'
  `sha256` and `lines` (from `extract_items.py --json`) and the docstring line
  references. Give each corrected `DISCREPANCY` item its final status (for example
  `A/seed_certificate/prose/012` becomes `PROOF` once M11 is fixed). Refresh the
  stale numbers in `companion/current_verification.tex` ("2026 Lean names").
- Then a new release run (`editorial/build.sh` and the release scripts; needs TeX,
  Node.js and Poppler) to refresh `release/` and the receipts.
- Step 3 is the author's expert check.

## Left on the Linux machine (nothing needed)

- The six paused agent sessions; their notes are in the repository.
- `~/MyProjects/BFGS-nonsmooth/pause_notes/`: the coordinator's note (superseded
  by this file) and the original agent notes (copied into the repository).
- `~/MyProjects/BFGS-nonsmooth/AGENTS.md`: the pruning preference, now in
  `AGENTS.md`.
- Build outputs (`.lake/`, `paper/build/`, `companion/build/`), rebuilt on the Mac.
