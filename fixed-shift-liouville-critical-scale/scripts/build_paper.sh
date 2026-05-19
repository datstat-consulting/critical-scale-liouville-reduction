#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../paper"
pdflatex -interaction=nonstopmode -halt-on-error critical_scale_reduction_fixed_shift_liouville_pair_correlations.tex
pdflatex -interaction=nonstopmode -halt-on-error critical_scale_reduction_fixed_shift_liouville_pair_correlations.tex
