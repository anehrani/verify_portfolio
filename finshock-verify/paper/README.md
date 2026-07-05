# Paper

This directory contains a complete first draft of the FinShockVerify paper:

- `main.tex`: paper source
- `references.bib`: bibliography

The draft is written as an artifact paper for the current MVP. It is honest
about what has been proved so far and frames the next publishable extension:
multi-asset rebalancing with transaction costs and finite expected shortfall.

## Build

If LaTeX is installed:

```sh
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

This workspace currently does not have `pdflatex` or `bibtex` installed, so the
PDF was not rendered locally.
