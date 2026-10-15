# Handoff: resuming on another machine (14 October 2026)

Written by the coordinating agent (Claude in OpenCode) on the author's Linux
machine, at the author's request, to continue on the author's MacBook with
OpenCode and the same model. Standing instructions: `AGENTS.md`.

## State (updated 15 October 2026, on the MacBook)

The work moved from the Linux machine to the MacBook on 14 October and resumed there
the same day.

| Work | State | Details |
|---|---|---|
| Lean review, passes 1–4 | done | `TODO_LEAN_REVIEW.md`, `bfgs_lean_article/README.md` |
| Manuscript review | M1–M6 fixed on 13 October; M7–M29 (from M12 on in the companion) and the companion's wording points W1–W43, found by the Lean coverage, stay open until step 2 | `TODO_MANUSCRIPT_REVIEW.md` |
| Lean coverage, article | complete: all 616 items classified; 15 coverage modules, each reviewed by an independent agent, imported and audited | `TODO_LEAN_COVERAGE.md` |
| Lean coverage, companion | complete (14 and 15 October): all 1856 items classified; 18 coverage modules in twelve groups, each reviewed by an independent agent, fixed, committed and imported | `TODO_LEAN_COVERAGE.md`, `editorial/lean_coverage/` |

Next: the end of the companion phase (step 5 under "Resuming the companion
coverage"): the axiom audit and the kernel replay on a clean tree.

Latest checks:

- Axiom audit of commit `a2028c9` on a clean tree: PASS. 3862 declarations (every
  ledger, coverage-register and package name) use only `propext`,
  `Classical.choice` and `Quot.sound` (`bfgs_lean_article/AXIOM_AUDIT.json`).
- Kernel replay of `023f555` with lean4checker v4.19.0: PASS, 749 modules
  (`bfgs_lean_article/KERNEL_REPLAY.json`). It predates the coverage modules;
  rerun it at the end of the companion phase.
- `lake build` in `bfgs_lean_article` succeeds with no warnings from the coverage
  modules (last run on 15 October with every companion module: 104 s);
  `check_coverage.py` exits 0 (also with `--strict --allow-discrepancies` on every
  article and companion file); `generate_companion.py --check` passes.

## Setting up the Mac

1. Tools:
   - Command line tools: `xcode-select --install` (git, clang).
   - Homebrew, then `brew install python@3.12 gh`. The scripts need Python 3.11 or
     newer, and macOS's own `python3` is older: call `python3.12`, or put
     Homebrew's Python first in `PATH`. (On the MacBook, Homebrew's `python3` is
     3.14 and is first in `PATH`, so plain `python3` works.)
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

   On macOS 26 the `cache` executable fails with `dyld: __DATA_CONST segment
   missing SG_READ_ONLY flag` (exit 134): the old `ld64.lld` bundled with Lean
   4.19.0 links it, and the new dyld rejects the result. Link it with the system
   linker instead (remove a binary left by a failed attempt first):

       rm -f .lake/packages/mathlib/.lake/build/bin/cache
       LIBRARY_PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.19.0/lib" LEAN_CC=/usr/bin/clang lake exe cache get

   Library builds link no executable and need nothing special. On the MacBook
   (Apple M5, 10 cores, 32 GB) the whole `lake build` took 12.5 minutes, with the
   default thread count, and ended with the main library's 1244 style warnings.
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
      is judged; accepted ones go to `TODO_MANUSCRIPT_REVIEW.md` (the numbering
      continues after the highest M and W numbers there);
   4. add `import BfgsArticle.Coverage.Companion.<Name>` to
      `bfgs_lean_article/BfgsArticle.lean`; while no agent runs Lean,
      `lake build BfgsArticle.Coverage.Companion.<Name>`, then
      `lake build BfgsArticle` (no warnings from coverage files). In waves 1 and 2
      agents ran Lean all the time, so the coordinator checked each module with
      `LEAN_NUM_THREADS=4 lake env lean <file>` (no errors, no warnings), added the
      root import in the group's commit, and ran the full `lake build` once, before
      wave 3;
   5. commit ("Lean coverage of companion chapter … (independently reviewed)")
      and push.
4. **Wave 2:** compTA, compG, compFQ, compU (no pause notes). **Wave 3:** compI
   (`01_I.tex`, `research_story.tex`) and compE (`14_E.tex`,
   `current_verification.tex`, `correspondence.tex`), the planned compFront split
   in two, after all chapters, since they map onto chapter items.
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

   On macOS 26, build lean4checker with the system linker, as for the Mathlib
   cache: `LIBRARY_PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.19.0/lib"
   LEAN_CC=/usr/bin/clang lake build`. Once linked, `test.sh` and the replay run
   it without these variables (checked on 14 October 2026).

## Findings of the companion coverage

The findings of the twelve groups are recorded: the companion's discrepancies as
M12–M29 and its wording points as W1–W43 in `TODO_MANUSCRIPT_REVIEW.md` (the
recurrences in Chapters 1 and 13 and in the research story are listed under M8, M12
and M24), and the possibly vacuous run statements of Chapter 7 in
`TODO_LEAN_REVIEW.md`. The pause notes of 14 October stay in
`editorial/lean_coverage/pause_notes/` as a record; their tentative findings were
all settled by the chapter groups.

## After the Lean coverage

- **Step 2:** the line-by-line reading of the article's proofs, and the manuscript
  corrections (M7 onwards, and the wording points W1 onwards). After each TeX edit,
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
