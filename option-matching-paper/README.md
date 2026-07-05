# Revised option-matching paper

This directory contains an evidence-aligned revision of
`verified_option_matching_paper.tex` and a buildable Rocq prototype copied from
the workspace's original `src/example.v`.

## Files

- `main.tex` - revised manuscript source
- `main.pdf` - rendered 18-page manuscript
- `OptionMatchingPrototype.v` - Rocq 9.1-compatible prototype
- `Audit.v` - assumption-printing harness for completed headline results
- `verification_ledger.csv` - declaration-level faithfulness classification
- `_CoqProject`, `Makefile` - reproducible proof build
- `REVISION_NOTES.md` - substantive changes and remaining work

## Verify the proof artifact

```sh
make build
make audit
```

The audit intentionally reports six admitted declarations in the transitive
module context. They are classified as placeholders and are not counted as
completed paper contributions.

## Rebuild the manuscript

The manuscript was rendered with Tectonic 0.16.9:

```sh
tectonic main.tex
```

Do not retitle the manuscript as a fully verified mechanism until the
placeholder count is zero and the end-to-end headline theorems have been
audited against their paper statements.
