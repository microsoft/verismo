# Monthly Verus Bump — Design

## Problem

Verismo pins Verus in two coupled places. A bump must change both, together:

| Location | Pinned values |
| --- | --- |
| `source/Cargo.toml` | `verus_builtin`, `verus_builtin_macros`, `verus_state_machines_macros`, `vstd`, `verus_syn` — all pinned `=0.0.0-YYYY-MM-DD-HHMM` |
| `tools/install_verus` | `VERUS_VERSION`, `DEFAULT_VERUS_REV`, `VERUS_RUST_VERSION` |

The two sources use different version formats and are published independently:

- crates.io publishes `0.0.0-2026-08-02-0125`.
- The Verus repo tags `release/0.2026.08.02.b677dd5`.

They correspond **by date**. Verus tags releases roughly weekly, but crates.io
publishes less often, so not every release has matching crates. A valid bump
target is therefore a date present in *both* sources.

Bumps also break proofs in ways that are invisible from the version numbers.
The 2026-07-27 → 2026-08-02 bump upgraded the bundled Z3 from 4.12.5 to 4.16.0
([verus-lang/verus#2578](https://github.com/verus-lang/verus/pull/2578)), and
`proof_align_down` stopped verifying: it had been relying on the solver to
derive the nonlinear identity `val - val % align == val / align * align` on its
own. The repair was a one-line `proof_div_mod_rel` call. Finding that repair
requires judgment; finding the target version does not.

That asymmetry drives the design.

## Approach

A deterministic shell script does the mechanical work. An agent does only the
part that needs judgment.

Rejected alternatives:

- **Fully agentic.** Version selection becomes non-deterministic and
  untestable, and the workflow spends model credits every month even when
  there is nothing to update.
- **Two workflows** (mechanical bump PR, plus a separate agent reacting to CI
  failure). Doubles the moving parts, and the proof repair lands as a follow-up
  instead of in the same PR.

## Components

### 1. `tools/bump_verus.sh`

Deterministic, no AI, runnable by hand.

**Discover.** Find the newest date published as *all five* crates on crates.io
and as a non-rolling Verus release. Requiring all five guards against a
partially published date. Rolling pre-releases (`release/rolling/...`) are
excluded.

**Resolve.** From the chosen release: the short tag SHA expands to the full
40-character SHA via the GitHub API, and `rust-toolchain.toml` at that revision
gives `channel`, which is `VERUS_RUST_VERSION`.

**Apply.** Rewrite the five pins in `source/Cargo.toml` and the three variables
in `tools/install_verus`.

**Report.** Print old and new versions. Exit `0` when files were updated and
`3` when already current, so the caller can skip the rest of the run without
parsing output. Any other non-zero exit is a genuine error.

Flags:

- `--check` — discover and report, make no edits.
- `--to <YYYY-MM-DD>` — target a specific date instead of the newest, for
  testing and manual use.

`VERUSFMT_VERSION` is out of scope: verusfmt is a separate project on its own
release cadence.

### 2. `.github/workflows/verus-bump.md`

The agentic workflow source.

```yaml
on:
  schedule:
    - cron: "0 6 1 * *"     # 1st of each month, 06:00 UTC
  workflow_dispatch:
permissions:
  contents: read
  pull-requests: read
  copilot-requests: write
network:
  allowed: [defaults, rust, github]
tools:
  edit:
  bash: ["cargo:*", "rustup:*", "git:*", "curl", "unzip", "sed", "grep", "cat", "ls", "./tools/fmt.sh"]
safe-outputs:
  create-pull-request:
    title-prefix: "[verus-bump] "
    labels: [dependencies, verus, automated]
    draft: true
    if-no-changes: "ignore"
timeout-minutes: 60
max-turns: 40
```

`network.allowed` covers crates.io and rustup (`rust`) and the Verus release
zips (`github`). Anything not listed is blocked *and* redacted from run output.

`permissions.copilot-requests: write` bills inference to the organization and
requires the org Copilot policy to be enabled. Without that policy, the
fallback is a `COPILOT_GITHUB_TOKEN` repository secret.

### 3. `.github/workflows/verus-bump.lock.yml`

Compiled from the `.md` by `gh aw compile`, and committed. GitHub Actions
executes the lock file, not the markdown. Frontmatter changes require
recompilation; prompt-body changes do not.

## Data flow

```
cron (monthly)
  └─ steps: tools/bump_verus.sh          # outside the agent sandbox
       ├─ already current ─→ write `noop` to $GH_AW_SAFE_OUTPUTS ─→ done, no agent
       └─ new version ─→ edit pins ─→ ./tools/install_verus --use-prebuilt
            └─ agent
                 ├─ cargo verus focus --release -- --multiple-errors=20
                 ├─ repair broken proofs (iterate)
                 ├─ ./tools/fmt.sh --check
                 └─ write PR body
                      └─ gh-aw safe_outputs job ─→ draft PR
```

Writing `noop` from the `steps:` block skips agent inference entirely, so a
month with no new release costs nothing.

The agent never pushes. It edits the workspace; gh-aw packages the result as a
git bundle and a separate permission-controlled job creates the branch and PR.

## Guardrails

This is a verification project, so the failure mode that matters is not a
broken build — it is a proof that passes because it was weakened.

The agent is forbidden from:

- introducing `assume(...)`,
- adding `#[verifier::external_body]` or
  `#[verifier::exec_allows_no_decreases_clause]`,
- deleting or relaxing any `ensures`, `requires`, `invariant`, or `decreases`
  clause,
- weakening a postcondition to match whatever the solver happens to prove.

Permitted repairs add proof *steps*: lemma calls, `assert ... by (...)`,
explicit witnesses. The `proof_div_mod_rel` fix is the model — it stated a fact
the solver used to infer, and changed no contract.

If the agent cannot repair a failure honestly, it leaves it failing and
documents it. A failing draft PR is a good outcome; a green PR with a hollowed
proof is not.

## Error handling

| Situation | Behavior |
| --- | --- |
| No newer version | `noop`, no PR, no agent run |
| Bump verifies clean | Draft PR, mechanical diff only |
| Bump breaks proofs, agent repairs them | Draft PR explaining each repair |
| Bump breaks proofs, agent cannot repair | Draft PR with failures documented |
| Version discovery fails (API error, no common date) | Job fails loudly; no PR |

Every PR is a draft — `draft: true` is a gh-aw policy the agent cannot
override. The PR body states old → new versions, notable upstream deltas such
as a Z3 upgrade, which proofs broke, what was changed and why, and what remains
failing.

Discovery failure fails the job rather than opening a PR, because a
half-discovered version would produce a misleading diff.

## Testing

`bump_verus.sh` holds the logic worth testing and is exercised directly:

- `--check` against the live APIs reports the current target without editing.
- `--to 2026-07-27` applies a known historical version, so the edit logic is
  verified against a real, previously-shipped configuration.
- Re-running when already current exits `3` and leaves the tree unchanged.

The workflow itself is validated with a `workflow_dispatch` run.

## Operational notes

- GitHub disables scheduled workflows after 60 days of repository inactivity.
  A monthly cron on an active repository is unaffected, but a dormant period
  will silently stop it.
- Creating PRs from Actions requires "Allow GitHub Actions to create and
  approve pull requests" in repository settings.
- `timeout-minutes: 60` is generous against a verification run that currently
  takes about five minutes in CI, leaving room for several repair iterations.
