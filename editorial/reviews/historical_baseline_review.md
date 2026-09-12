# Historical original-release verification

The unchanged original public gate cannot serve as a whole-repository gate for the later journal project. Its citation-preservation check uses a repository-wide Git diff for every tracked Lean file against `06ee12f7e7661437b8481fcab3b5bd26cff60130`. The article project deliberately adds independently audited Lean files under `editorial/`, so this historical citation-only assertion fails even though the original proof inputs and sealed report are unchanged.

`editorial/verify_historical_baseline.py` preserves that failure and runs the entire original gate in its proper historical context. It creates two clean detached Git worktrees: one at the calling repository's exact committed HEAD, and one at the frozen original-release commit `00362c0249262d182866f14bac756a7c4edac95c`. It does not patch, skip, relax or replace any old assertion. Before either public gate runs, it compares the full frozen audit input register and every sealed original artifact between the two snapshots, including the validator scripts themselves.

The final actual run `editorial/historical_baseline/runs/20260912_baseline_gate_02` established:

- Committed HEAD `0fadf4e8cf0ed2701cdf8841a3773b123f636953`: the old gate exits 1 at the unchanged citation checker, which flags 13 newly added editorial Lean files.
- All **761 historical compiler/audit inputs** and **286 sealed original artifacts** match their frozen hashes in both snapshots.
- Historical commit `00362c0`: the complete unmodified public gate passes, including textual regeneration, compiler/axiom evidence, citation preservation, full correspondence, corruption-rejection tests, index navigation, PDF/render evidence and the complete artifact manifest.
- Both detached worktrees remain clean through validation and are removed successfully afterward. No historical source, validator, cache or toolchain is copied into the working project. No Lean build is represented as having been performed by this evidence-validation gate.

Every command has a timestamp, working directory, exit code, separate stdout/stderr logs and their hashes. The successful historical gate output, the complete frozen-file hash comparison, wrapper hash and cleanup record are retained in the run directory. The current-HEAD failure log remains explicit evidence rather than being overwritten with the baseline PASS.

The final run completed at `2026-09-12T09:28:13.149716+00:00` with 19 commands and 38 individually hashed stdout/stderr logs. Its wrapper SHA-256 is `112bc8aba1ee090b24a8eff6f001f947c8fb7a1d1e48959b6719b829540add2f`. Its command-register SHA-256 is `4d26c9d68d05827d69a916e9bd96bbe1151280e2e1c243e4df2fcd36e2885c21`. Every recorded command-log hash, the frozen comparison hash and the wrapper hash were independently rechecked after completion.

The earlier successful run `20260912_baseline_gate_01` is retained unchanged as historical evidence for the initial wrapper version. An independent review found no blocking weakening or false-PASS route in that version and confirmed its complete log integrity. It identified two nonblocking failure-path robustness issues: work-directory initialization could fail before writing a summary, and a failed checkout could register a worktree before it reached the successful-creation list. The final wrapper moves owned work-directory initialization inside the guarded run, records attempted owned checkout paths before creation, inspects Git registration during cleanup, and records cleanup exceptions as failures. Cleanup still touches only this run's own paths and never forces deletion. The final run above exercised the resulting ordinary success and cleanup paths; it did not simulate every filesystem or Git failure mode.

For a fresh archive extraction, restore the delivered Git bundle first, then invoke the wrapper from the repository root:

```bash
python3 _archive/restore_git_history.py
python3 editorial/verify_historical_baseline.py
```

For an existing Git checkout, only the second command is needed. Node.js is required by the original functional index check; `--node /path/to/node` selects it explicitly. `--run-id NAME` chooses a new log directory without overwriting an earlier run. The baseline commit is fixed in the wrapper. Missing Git history, changed frozen inputs, unexpected global Lean changes, failure at a different assertion, failure of the historical gate, or failed worktree cleanup causes the wrapper to fail.

This is **committed-snapshot historical verification**. It does not certify uncommitted workspace edits, the new article/companion correspondence, or the supplemental article Lean proofs. The current editorial release gates and fresh audits remain separate requirements. The source archive must retain the baseline and its earlier citation-comparison history, which the delivered Git bundle provides.
