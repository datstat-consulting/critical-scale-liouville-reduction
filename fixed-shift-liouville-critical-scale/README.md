# Critical-scale reductions for fixed-shift Liouville pair correlations

This repository accompanies the manuscript

**Critical-scale reduction for fixed-shift Liouville pair correlations**.

It contains the paper source, a compiled PDF, and a Lean 4 formalization of the
main deterministic reduction lemmas used in the manuscript.

> **Scope.** This repository represents the first half of the project: the
> deterministic reduction framework. It formalizes and documents the reduction
> from fixed-shift Liouville pair-correlation cancellation to critical-scale
> first-moment/local-`U²` and projected-packet criteria. The complementary
> analytic half—ruling out the remaining projected/local-`U²` packet obstruction
> for the Liouville sequence—is isolated here but is not claimed as completed in
> this repository.

## Main content

The repository should be read as **Part I: deterministic reductions**. For a
fixed nonzero shift `h`, the paper studies the derived sequence

\[
a_h(n)=\lambda(n)\lambda(n+h)
\]

and develops critical-scale criteria at `H = X^{1/2}`. The checked Lean file
formalizes the deterministic implication chain, including the corrected
local-`U²` bridge: the false linear estimate is replaced by the fourth-power
estimate

\[
|B_a(x;M)|^4\le 3M^4\,\mathcal U_2(\widetilde a; I_{x,M}),
\]

together with the Young/Hölder-style averaging route to the first-moment
criterion.

## Contents

### `paper/`

- `critical_scale_reduction_fixed_shift_liouville_pair_correlations.tex` — manuscript source.
- `critical_scale_reduction_fixed_shift_liouville_pair_correlations.pdf` — compiled manuscript.
- `tex_original_to_patched.diff` — diff from the earlier TeX source to the current fourth-power-corrected version.

### `lean/`

- `FixedShiftLiouville_pass126.lean` — archived checked Lean file.

### repository root

- `FixedShiftLiouville.lean` — Lean entry point used by Lake.
- `lakefile.lean` — minimal Lake project file.
- `lean-toolchain` — Lean version pin.
- `AI_USE.md` — AI-use disclosure.
- `logs/pass126_check.log` — Lean check log for the current proof file.

## Lean formalization status

The Lean development verifies the deterministic framework used in Part I. It is
not presented as a formal proof of the still-open analytic input needed to close
the fixed-shift Chowla problem.

The checked Lean artifact has:

- zero `sorry` statements;
- zero `admit` statements;
- zero `axiom` declarations;
- a successful Lean 4.29.1 check, with warnings only.

The verification log is included at:

```text
logs/pass126_check.log
```

The exact checked source is also duplicated as:

```text
lean/FixedShiftLiouville_pass126.lean
```

## Building the Lean file

Install Lean 4 via `elan`, then from the repository root run:

```bash
lake update
lake exe cache get
lake build FixedShiftLiouville
```

The submitted check was performed with Lean 4.29.1 and a Mathlib cache matching
that toolchain.

For a direct non-Lake check in an already configured environment:

```bash
lean FixedShiftLiouville.lean
```

## Building the paper

From the repository root:

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error critical_scale_reduction_fixed_shift_liouville_pair_correlations.tex
pdflatex -interaction=nonstopmode -halt-on-error critical_scale_reduction_fixed_shift_liouville_pair_correlations.tex
```

## AI-use disclosure

AI tools were used only for:

- Lean proof engineering and proof repair;
- literature review support;
- TeX cleanup, polishing, and correction;
- consistency checks between the manuscript and Lean formalization.

See [`AI_USE.md`](AI_USE.md) for the full disclosure.
