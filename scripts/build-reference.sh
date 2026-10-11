#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
build_dir="$(mktemp -d)"
trap 'rm -rf "$build_dir"' EXIT
latexmk -norc -pdf -pdflatex='pdflatex -no-shell-escape %O %S' \
  -interaction=nonstopmode -halt-on-error -outdir="$build_dir" reference/parikh_theorem.tex
cp "$build_dir/parikh_theorem.pdf" reference/parikh_theorem.pdf
