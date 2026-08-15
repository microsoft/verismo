---
description: Monthly bump of the pinned Verus version, repairing any proof breakage it causes.

"on":
  schedule:
    - cron: "0 6 1 * *"
  workflow_dispatch:
    inputs:
      target_date:
        description: "Release date to bump to (YYYY-MM-DD). Defaults to the newest."
        required: false
        type: string

permissions:
  contents: read
  pull-requests: read
  copilot-requests: write

network:
  allowed:
    - defaults
    - rust
    - github

tools:
  edit:
  bash:
    - "cargo:*"
    - "rustup:*"
    - "git:*"
    - "./tools/fmt.sh"
    - "curl"
    - "unzip"
    - "sed"
    - "grep"
    - "cat"
    - "ls"

safe-outputs:
  create-pull-request:
    title-prefix: "[verus-bump] "
    labels: [dependencies, verus, automated]
    draft: true
    if-no-changes: "ignore"

timeout-minutes: 60
max-turns: 40

steps:
  - name: Apply the version bump
    id: bump
    env:
      GH_TOKEN: ${{ github.token }}
      GH_AW_SAFE_OUTPUTS: ${{ steps.set-runtime-paths.outputs.GH_AW_SAFE_OUTPUTS }}
      TARGET_DATE: ${{ inputs.target_date }}
    run: |
      set -uo pipefail
      args=()
      if [ -n "${TARGET_DATE:-}" ]; then
        args+=(--to "$TARGET_DATE")
      fi
      status=0
      ./tools/bump_verus.sh "${args[@]}" || status=$?
      case "$status" in
        0)
          echo "updated=true" >> "$GITHUB_OUTPUT"
          ;;
        3)
          echo "updated=false" >> "$GITHUB_OUTPUT"
          mkdir -p "$(dirname "$GH_AW_SAFE_OUTPUTS")"
          echo '{"type":"noop","message":"Verus is already at the newest version published on both crates.io and as a release."}' >> "$GH_AW_SAFE_OUTPUTS"
          ;;
        *)
          exit "$status"
          ;;
      esac

  - name: Install the new Verus toolchain
    if: steps.bump.outputs.updated == 'true'
    working-directory: tools
    run: ./install_verus --use-prebuilt
---

# Monthly Verus Bump

The version pins have **already been updated for you** by the previous step.
`git diff` shows exactly what changed in `source/Cargo.toml` and
`tools/install_verus`, and the matching Verus toolchain is already installed.

Your job is to make the repository verify again at the new version, and to
explain what you did.

## What to do

1. Run `git --no-pager diff` to see which versions changed.
2. From `source/`, run:
   `cargo verus focus --release -- --multiple-errors=20`
3. If it reports `0 errors`, go to "Opening the pull request".
4. Otherwise repair each failure, re-running verification after each change.
5. When verification passes, run `./tools/fmt.sh` from the repository root and
   include any reformatting in your changes.

## How to repair a broken proof

A Verus upgrade may break the existing proofs due to different reasons, for example:
1. need extra proof for z3 solver: the statement is still true but the proof misses some facts (e.g., asserts, lemmas or triggers) explicitly;
2. vstd API changes.
3. wrong spec: very low likely.

Prioritize to fix proofs by considering case 1 and 2. Only try case 3 to fix
proof by modifying the spec statement if you can figure out a counterexample.

## Rules you must not break

This is a formal verification project. A proof that passes because it was
weakened is far worse than a proof that visibly fails.

You must **never**:

- introduce `assume(...)`;
- add `#[verifier::external_body]`, `#[verifier::external]`, or
  `#[verifier::exec_allows_no_decreases_clause]`;
- delete or weaken any `ensures`, `requires`, `invariant`, or `decreases`
  clause;
- change a specification so it matches whatever the solver happens to prove;
- comment out, `#[ignore]`, or delete a proof to make verification pass.

Only add proof steps that help the solver establish the **existing**
specification.

The one exception is case 3 above. You may change a specification **only** if
you can state a concrete counterexample showing the existing specification is
actually wrong. If you do, you must give that counterexample in the pull
request under a heading **"Specification changed"**, along with the old and new
statements. A specification change without a counterexample is never
acceptable — if you merely suspect a specification is wrong, leave the proof
failing and say so instead.

If you cannot repair a failure within these rules, **leave it failing** and
document it in the pull request. That is a good outcome.

## Opening the pull request

Open a pull request whether or not verification passes. It is created as a
draft either way.

Title: `Update Verus to the <release date> release`

The body must contain:

- the old and new versions, for both the crates.io pins and `VERUS_VERSION`;
- any notable upstream change that explains breakage — check the Verus commit
  log between the two revisions for toolchain or Z3 upgrades, which you can
  read with
  `curl -sS https://api.github.com/repos/verus-lang/verus/compare/<old-rev>...<new-rev>`
  (or the GitHub tools available to you);
- for each proof you repaired: which proof, why it broke, and what you added;
- a **"Specification changed"** section if you changed any specification, with
  the counterexample that justified it;
- a clearly marked **"Still failing"** section listing anything unresolved,
  with the error output. Omit this section only if verification is clean.

Do not describe a run as passing unless you saw `0 errors` in the output.
