# Contributing to bfo-to-lean

This repository is a **generated artifact**, snapshotted from an upstream private source repository on each release. Pull requests opened here are not actioned — the next snapshot publish would overwrite anything merged. Please file an **issue** instead.

## How to contribute

1. Open a GitHub Issue describing the bug or improvement. For converter bugs, include a minimal repro (a small CLIF snippet plus expected and actual Lean output is ideal).
2. If you have a proposed patch, paste it as a fenced diff in the issue body, or attach a `.patch` file.
3. A maintainer will action the issue upstream and the change will ship in a later release of this package.

## Attribution

When a contributed change ships, the maintainer credits the contributor by `@mention` and issue number in the public Release notes for that version.

GitHub's contribution graph won't reflect this — that's by design, since the commit landing here is a squashed snapshot, not your patch verbatim. The issue thread plus the Release-notes acknowledgment is the substantive credit.

## What gets in

- Bug reports against the generated `BFO.lean`, with a CLIF→Lean diff demonstrating an unfaithful translation.
- Bug reports against the converter (parser, lint, translation rules).
- Translation-rule improvements.
- Tooling fixes (lakefile, manifest, CI workflow).
- Documentation improvements.

## What we cannot accept

- Pull requests against this repository. Open an issue with the diff in the body instead.
- Changes to the vendored BFO source under `vendor/bfo-source/` — those come from upstream via `bin/refresh-bfo-source <sha>`.

## Questions

Use GitHub Discussions if it's enabled on this repo; otherwise open an Issue on the Issues tab.
