# Independent Verus Version Selection

## Goal

Update every Verus crates.io dependency and the installed Verus toolchain to
the newest version available from its own source. Do not require crate
versions to match one another or the Verus release date.

## Version selection

The bump script treats these six targets independently:

- `vstd`
- `verus_builtin`
- `verus_builtin_macros`
- `verus_state_machines_macros`
- `verus_syn`
- the stable, non-rolling Verus GitHub release

For each crate, select its newest non-yanked dated version from crates.io. For
the toolchain, select the newest stable, non-rolling GitHub release. A missing
publication for one crate does not prevent other crates or the toolchain from
advancing.

With `--to YYYY-MM-DD`, apply the date as an inclusive upper bound to every
target independently. Select each target's newest version dated on or before
that date. Fail explicitly if any target has no eligible version.

## Applying updates

Read and compare all five current Cargo pins and the current `VERUS_VERSION`.
An update is available when any selected target differs from its current pin.

Rewrite each workspace dependency by crate name, preserving its other
features and options. Update `VERUS_VERSION`, `DEFAULT_VERUS_REV`, and
`VERUS_RUST_VERSION` from the independently selected GitHub release. Assert
that every expected replacement was applied exactly once so a changed file
shape cannot silently produce a partial update.

Output must list the current and target version for each crate and the
toolchain. Exit code `3` means all six targets are already current; exit code
`0` means at least one target can be or was updated.

## Workflow and documentation

The monthly workflow continues to run the bump script, install the selected
toolchain, verify the repository, and create a draft pull request. Its prompt
must report old and new versions per crate rather than referring to one shared
crates.io pin.

Update user-facing documentation to say that crate and toolchain versions are
selected independently.

## Error handling

Network, API, malformed-version, unresolved-commit, and missing-Rust-toolchain
errors remain fatal. A crate with no version under the requested date cutoff
is also fatal. The script must never silently retain a current pin because
discovery failed.

## Testing

Offline unit tests cover:

- independently selected versions when only some crates have a newer publish;
- independent stable release selection;
- inclusive `--to` cutoff behavior;
- mixed-version Cargo rewrites by crate name;
- detection of updates in any one of the six targets;
- no-op detection only when all six targets match;
- failure when any source has no eligible version.

The generated workflow is recompiled and validated after its source changes.
