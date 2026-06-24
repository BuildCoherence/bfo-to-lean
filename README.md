# BFO To Lean

Converter from the [Basic Formal Ontology
(BFO 2020)](https://github.com/BFO-ontology/BFO-2020) Common Logic
(CLIF) axiomatization to Lean 4. Developed to enable
[Axiom](https://axiomreason.com) users to use BFO, and made freely
available here.

The committed `BFO.lean` is a pure function of two inputs — the
pinned upstream BFO source under `vendor/bfo-source/` and this
converter's own code. CI re-runs the converter on every PR and asserts
byte-identical output; that is the mechanically-enforced faithfulness
claim.

## Layout

- `BFO.lean` — the generated deliverable, committed to the subtree.
- `Main.lean`, `BfoToLean/` — converter source.
- `Theorems.lean` — BFO theorems library (structural fidelity witnesses
  + canonical demo scenarios) covering the third CI fidelity check;
  built by `lake build`. Determinism + completeness checks run via
  `lake test` (the `convert --check` driver).
- `bin/refresh-bfo-source <sha>` — re-vendor the BFO source at a
  given upstream commit SHA. The only path that mutates `vendor/`.
- `bin/verify-bfo-source` — vendor audit; CI runs it on pin-bump PRs.
- `vendor/bfo-source/` — pinned upstream BFO CLIF, with
  `.provenance.json` recording the commit SHA and `LICENSE` carrying
  the CC BY 4.0 text.

## Usage

```
lake build                  # build the converter
lake exe convert            # regenerate BFO.lean from vendor/bfo-source
lake test                   # run the fidelity suite
bin/refresh-bfo-source <sha>  # re-vendor BFO source at a new SHA
```

A fresh clone with `elan` installed picks up the pinned Lean toolchain
from `lean-toolchain` automatically.

## Licenses

- Converter source: [MIT](LICENSE).
- Vendored upstream BFO source under `vendor/bfo-source/`:
  [CC BY 4.0](vendor/bfo-source/LICENSE).
- Generated `BFO.lean`: CC BY 4.0 derivative; the attribution travels
  in the file's provenance header.
